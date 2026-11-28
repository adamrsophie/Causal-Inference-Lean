/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.Efficiency.CrossFittingRate
public import CausalInference.Efficiency.CrossFittingExamples
public import CausalInference.PointTreatment.CellProportionScore

/-!
# Cross fitting with a fitted score and a fitted regression

Here both nuisance functions of the cross fitted estimator are fitted on the training data of
each fold, for a finite covariate.

**The cell proportion score.** For training data `t`, the fitted score at the covariate value
`w` is the proportion of treated units among the training units with covariate `w`, and `1/2` on
an empty cell (`cellPropFit`). On the first `n` units of a sample it is the cell proportion
score `cellScore` of `CausalInference.PointTreatment.CellProportionScore`
(`cellScore_eq_cellPropFit`). It is clipped to `[ε', 1 - ε']` (`clippedCellScore`), so that
it satisfies the bounds of the fitted score; when the true score lies in the interval, clipping
does not increase the error.

**The `√n` rate.** When every cell `{W = w}` has positive probability and the training sets of
the fold have at least `c n` units for a `c > 0`, `√n ‖ê_{n,k} - e‖₂` is bounded in probability
(`boundedInProbabilityENNReal_sqrt_mul_fitError_clippedCellScore`). At each `w`,
`p̂(w) - e(w) = (Ū - e(w) D̄) / D̄` with `D̄` the training mean of `1{W = w}` and `Ū` that of
`1{W = w, A = 1}`; the numerator is a mean of a variable of mean `0`, of order `N^{-1/2}` by
Chebyshev's inequality, and the denominator tends to `P(W = w) > 0`.

**The randomized population.** In the population of `CausalInference.Efficiency.BoundExamples`,
with the clipped cell proportion score (`ε' = 1/8`) and the cell mean regression fitted on the
other parity fold, every hypothesis of `tendstoInDistribution_crossFitArm` and of
`tendstoInDistribution_crossFitAte` holds: the score error tends to `0` with a `√n` rate, the
regression error tends to `0`, and the product condition follows from
`tendstoInMeasure_sqrt_mul_mul_of_bounded_left`. The estimators are asymptotically normal with
the efficient variances `5` and `19/3`.

## Main definitions

* `cellPropFit`, `clippedCellScore`: the cell proportion score on training data and its clipping.
* `twoPointScoreFit`: the clipped cell proportion score as a learner of the parity folds.

## Main results

* `cellScore_eq_cellPropFit`, `measurable_clippedCellScore`, `clippedCellScore_mem`.
* `boundedInProbability_sqrt_mul_cellPropFit_sub`,
  `boundedInProbabilityENNReal_sqrt_mul_fitError_clippedCellScore`.
* `tendstoInDistribution_crossFitArm_twoPoint_fittedScore`,
  `tendstoInDistribution_crossFitAte_twoPoint_fittedScore`.

## References

* V. Chernozhukov, D. Chetverikov, M. Demirer, E. Duflo, C. Hansen, W. Newey and J. Robins,
  *Double/debiased machine learning for treatment and structural parameters*, The Econometrics
  Journal 21 (2018).
-/

@[expose] public section

namespace CausalInference
namespace Efficiency

open MeasureTheory ProbabilityTheory MissingData PointTreatment Filter Finset
open scoped ENNReal Topology

variable {Ω' : Type*} {mΩ' : MeasurableSpace Ω'} {P : Measure Ω'}

section CellProportion

variable {𝒲 : Type*} [MeasurableSpace 𝒲]

/-- **The cell proportion score on training data**: for training data `t : S → 𝒲 × Bool × ℝ`,
the proportion of treated units among the training units with covariate `w`, and `1/2` on an
empty cell. -/
noncomputable def cellPropFit {S : Type*} [Fintype S] (t : S → 𝒲 × Bool × ℝ) (w : 𝒲) : ℝ :=
  if ∑ i, cellIndObs w (t i) = 0 then 1 / 2 else
    (∑ i, cellIndObs w (t i) * armIndObs true (t i)) / ∑ i, cellIndObs w (t i)

/-- **The clipped cell proportion score**: the cell proportion score projected onto
`[ε', 1 - ε']`. -/
noncomputable def clippedCellScore (ε' : ℝ) {S : Type*} [Fintype S] (t : S → 𝒲 × Bool × ℝ)
    (w : 𝒲) : ℝ :=
  clipInterval ε' (1 - ε') (cellPropFit t w)

omit [MeasurableSpace 𝒲] in
/-- On the first `n` units of a sample, the cell proportion score on training data is the cell
proportion score `cellScore` of the sample. -/
theorem cellScore_eq_cellPropFit {Ξ : Type*} (O : ℕ → Ξ → 𝒲 × Bool × ℝ) (n : ℕ) (ξ : Ξ)
    (w : 𝒲) : cellScore O n ξ w = cellPropFit (fun i : range n => O i ξ) w := by
  unfold cellScore cellPropFit sampleMean
  simp only [Finset.sum_coe_sort (range n) (fun i => cellIndObs w (O i ξ)),
    Finset.sum_coe_sort (range n) (fun i => cellIndObs w (O i ξ) * armIndObs true (O i ξ))]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · have hn' : ((n : ℝ))⁻¹ ≠ 0 := inv_ne_zero (by exact_mod_cast hn.ne')
    simp only [mul_eq_zero, hn', false_or]
    split_ifs
    · rfl
    · exact mul_div_mul_left _ _ hn'

omit [MeasurableSpace 𝒲] in
theorem clippedCellScore_mem {ε' : ℝ} (h : ε' ≤ 1 - ε') {S : Type*} [Fintype S]
    (t : S → 𝒲 × Bool × ℝ) (w : 𝒲) :
    ε' ≤ clippedCellScore ε' t w ∧ clippedCellScore ε' t w ≤ 1 - ε' :=
  clipInterval_mem h _

/-- The cell proportion score is jointly measurable in the training data and the covariate. -/
theorem measurable_cellPropFit [Countable 𝒲] [MeasurableSingletonClass 𝒲] {S : Type*}
    [Fintype S] : Measurable fun p : (S → 𝒲 × Bool × ℝ) × 𝒲 => cellPropFit p.1 p.2 := by
  refine measurable_from_prod_countable_left fun w => ?_
  have hN : Measurable fun t : S → 𝒲 × Bool × ℝ => ∑ i, cellIndObs w (t i) :=
    Finset.measurable_sum _ fun i _ => (measurable_cellIndObs w).comp (measurable_pi_apply i)
  have hU : Measurable fun t : S → 𝒲 × Bool × ℝ =>
      ∑ i, cellIndObs w (t i) * armIndObs true (t i) :=
    Finset.measurable_sum _ fun i _ => ((measurable_cellIndObs w).comp
      (measurable_pi_apply i)).mul ((measurable_armIndObs true).comp (measurable_pi_apply i))
  exact Measurable.ite (hN (measurableSet_singleton 0)) measurable_const (hU.div hN)

/-- The clipped cell proportion score is jointly measurable. -/
theorem measurable_clippedCellScore [Countable 𝒲] [MeasurableSingletonClass 𝒲] (ε' : ℝ)
    {S : Type*} [Fintype S] :
    Measurable fun p : (S → 𝒲 × Bool × ℝ) × 𝒲 => clippedCellScore ε' p.1 p.2 :=
  (continuous_clipInterval _ _).measurable.comp measurable_cellPropFit

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {A : Ω → Bool} {Y : Bool → Ω → ℝ} {W : Ω → 𝒲}
  {e : 𝒲 → ℝ} {μ : Measure Ω} [IsProbabilityMeasure μ] [MeasurableSingletonClass 𝒲]
  {K : ℕ} {O : ℕ → Ω' → 𝒲 × Bool × ℝ} [IsProbabilityMeasure P]

omit [MeasurableSpace 𝒲] [IsProbabilityMeasure μ] [MeasurableSingletonClass 𝒲] in
theorem abs_cellIndObs_le (w : 𝒲) (z : 𝒲 × Bool × ℝ) : |cellIndObs w z| ≤ 1 := by
  classical
  unfold cellIndObs
  rw [Set.indicator_apply]
  split_ifs <;> simp

omit [MeasurableSpace 𝒲] [IsProbabilityMeasure μ] [MeasurableSingletonClass 𝒲] in
theorem abs_armIndObs_le (a : Bool) (z : 𝒲 × Bool × ℝ) : |armIndObs a z| ≤ 1 := by
  unfold armIndObs
  split_ifs <;> simp

/-- **The `√n` rate of the cell proportion score at one cell.** For an i.i.d. sample with the
law of the observed data, a correct score, a cell `{W = w}` of positive probability and training
sets with at least `c n` units, `√n |p̂_{n,k}(w) - e(w)|` is bounded in probability. -/
theorem boundedInProbability_sqrt_mul_cellPropFit_sub (hW : Measurable W) (hA : Measurable A)
    (hY : ∀ a, Measurable (Y a)) (hps : IsPropensityScore μ A W e) (w : 𝒲)
    (hcell : 0 < μ.real (W ⁻¹' {w})) (hO : IsIIDSample O P)
    (hlaw : P.map (O 0) = μ.map (obsData A Y W)) (fold : ℕ → ℕ → Fin K) (k : Fin K) {c : ℝ}
    (hc : 0 < c) (htrain : ∀ᶠ n in atTop, c * n ≤ (cvTrain fold n k).card) :
    BoundedInProbability P (fun n ω =>
      √(n : ℝ) * |cellPropFit (trainingData fold O n k ω) w - e w|) := by
  set q := μ.real (W ⁻¹' {w}) with hqdef
  have hobs := measurable_obsData hW hA hY
  have hO0 := hO.aemeasurable 0
  have hg₂ : Measurable (cellIndObs (𝒲 := 𝒲) w) := measurable_cellIndObs w
  have hg₁ : Measurable fun z : 𝒲 × Bool × ℝ => cellIndObs w z * armIndObs true z :=
    hg₂.mul (measurable_armIndObs true)
  have hhm : Measurable fun z : 𝒲 × Bool × ℝ =>
      cellIndObs w z * armIndObs true z - e w * cellIndObs w z := hg₁.sub (hg₂.const_mul _)
  have hc₂ : ∀ ω, cellIndObs w (obsData A Y W ω) = (W ⁻¹' {w}).indicator 1 ω :=
    fun ω => cellIndObs_comp W A Y w ω
  have hc₁ : ∀ ω, cellIndObs w (obsData A Y W ω) * armIndObs true (obsData A Y W ω) =
      (W ⁻¹' {w}).indicator (respInd A) ω := fun ω => by
    change cellIndObs w (W ω, A ω, obsOutcome A Y ω) *
      armIndObs true (W ω, A ω, obsOutcome A Y ω) = _
    rw [cellIndObs_comp, armIndObs_comp, arm_true]
    by_cases h : W ω = w <;> simp [h]
  have hWs := hW (measurableSet_singleton w)
  have hI₂ : Integrable (fun ω => cellIndObs w (obsData A Y W ω)) μ := by
    simp only [hc₂]
    exact (integrable_const 1).indicator hWs
  have hI₁ : Integrable (fun ω => cellIndObs w (obsData A Y W ω) *
      armIndObs true (obsData A Y W ω)) μ := by
    simp only [hc₁]
    exact (integrable_respInd hA).indicator hWs
  have hE₂ : ∫ ω, cellIndObs w (obsData A Y W ω) ∂μ = q := by
    simp only [hc₂]
    rw [integral_indicator_one hWs]
  have hE₁ : ∫ ω, cellIndObs w (obsData A Y W ω) * armIndObs true (obsData A Y W ω) ∂μ =
      e w * q := by
    simp only [hc₁]
    rw [integral_indicator hWs, hps.setIntegral_respInd_cell hW hA w]
  -- the centered numerator has a `√N` rate
  have hh2 : MemLp (fun ω => cellIndObs w (O 0 ω) * armIndObs true (O 0 ω) -
      e w * cellIndObs w (O 0 ω)) 2 P :=
    memLp_comp_obs hW hA hY hO0 hlaw hhm (MemLp.of_bound (hhm.comp hobs).aestronglyMeasurable
      (1 + |e w|) (Eventually.of_forall fun ω => by
        rw [Real.norm_eq_abs]
        refine (abs_sub _ _).trans (add_le_add ?_ ?_)
        · rw [abs_mul]
          exact (mul_le_mul (abs_cellIndObs_le _ _) (abs_armIndObs_le _ _) (abs_nonneg _)
            zero_le_one).trans_eq (one_mul 1)
        · rw [abs_mul]
          exact mul_le_of_le_one_right (abs_nonneg _) (abs_cellIndObs_le _ _)))
  have hh0 : ∫ ω, (cellIndObs w (O 0 ω) * armIndObs true (O 0 ω) -
      e w * cellIndObs w (O 0 ω)) ∂P = 0 := by
    rw [integral_comp_obs hW hA hY hO0 hlaw hhm, integral_sub hI₁ (hI₂.const_mul _),
      integral_const_mul, hE₁, hE₂, sub_self]
  have hB := boundedInProbability_sqrt_card_mul_finsetMean hO hhm hh2 hh0
    (fun n => cvTrain fold n k)
  -- the denominator is consistent
  have hcard : Tendsto (fun n => (cvTrain fold n k).card) atTop atTop := by
    refine tendsto_natCast_atTop_iff.1 (tendsto_atTop_mono' atTop htrain ?_)
    exact tendsto_natCast_atTop_atTop.const_mul_atTop hc
  have hg₂2 : MemLp (fun ω => cellIndObs w (O 0 ω)) 2 P :=
    memLp_comp_obs hW hA hY hO0 hlaw hg₂ (MemLp.of_bound (hg₂.comp hobs).aestronglyMeasurable
      1 (Eventually.of_forall fun ω => by rw [Real.norm_eq_abs]; exact abs_cellIndObs_le _ _))
  have hD := isConsistent_finsetMean hO hg₂ hg₂2 hcard
  rw [integral_comp_obs hW hA hY hO0 hlaw hg₂, hE₂, IsConsistent,
    tendstoInMeasure_iff_dist] at hD
  -- the event bound
  intro η hη
  obtain ⟨M₁, hM₁, hB1⟩ := hB (η / 2) (ENNReal.half_pos hη.ne')
  have hD1 := (ENNReal.tendsto_nhds_zero.1 (hD (q / 2) (by positivity))) (η / 2)
    (ENNReal.half_pos hη.ne')
  have hsc : 0 < √c := Real.sqrt_pos.2 hc
  refine ⟨2 / (q * √c) * M₁, by positivity, ?_⟩
  filter_upwards [hB1, hD1, htrain] with n h1 h2 h3
  refine ((measure_mono ?_).trans (measure_union_le _ _)).trans
    ((add_le_add h1 h2).trans (ENNReal.add_halves η).le)
  intro ω hω
  simp only [Set.mem_ofPred_eq, Set.mem_union] at hω ⊢
  by_contra! hlt
  obtain ⟨hlt1, hlt2⟩ := hlt
  set N : ℝ := ((cvTrain fold n k).card : ℝ) with hNdef
  set D := ∑ i ∈ cvTrain fold n k, cellIndObs w (O i ω) with hDdef
  set U := ∑ i ∈ cvTrain fold n k, cellIndObs w (O i ω) * armIndObs true (O i ω) with hUdef
  have hsum : ∑ i ∈ cvTrain fold n k, (cellIndObs w (O i ω) * armIndObs true (O i ω) -
      e w * cellIndObs w (O i ω)) = U - e w * D := by
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
  rw [hsum] at hlt1
  have hND : q / 2 < N⁻¹ * D := by
    rw [Real.dist_eq] at hlt2
    have := (abs_sub_lt_iff.1 hlt2).2
    linarith
  have hN0 : 0 ≤ N := Nat.cast_nonneg _
  have hNpos : 0 < N := by
    rcases hN0.lt_or_eq with h | h
    · exact h
    · rw [← h, inv_zero, zero_mul] at hND
      linarith [show 0 < q / 2 by positivity]
  have hDpos : 0 < D := pos_of_mul_pos_right ((show 0 < q / 2 by positivity).trans hND)
    (inv_nonneg.2 hN0)
  have hfit : cellPropFit (trainingData fold O n k ω) w - e w = (U - e w * D) / D := by
    unfold cellPropFit trainingData
    simp only [Finset.sum_coe_sort (cvTrain fold n k) (fun i => cellIndObs w (O i ω)),
      Finset.sum_coe_sort (cvTrain fold n k)
        (fun i => cellIndObs w (O i ω) * armIndObs true (O i ω))]
    rw [← hDdef, ← hUdef]
    simp only [hDpos.ne', ↓reduceIte]
    field_simp
  rw [hfit] at hω
  have hDq : q * N < 2 * D := by
    have := mul_lt_mul_of_pos_left hND hNpos
    rw [← mul_assoc, mul_inv_cancel₀ hNpos.ne', one_mul] at this
    linarith
  have hsN : √N * √N = N := Real.mul_self_sqrt hN0
  have hrpos : 0 < √N := Real.sqrt_pos.2 hNpos
  have hcn : √c * √(n : ℝ) ≤ √N := by
    rw [← Real.sqrt_mul hc.le]
    exact Real.sqrt_le_sqrt h3
  have hkey : √(n : ℝ) * q * √c * √N ≤ 2 * D := by
    have := mul_le_mul_of_nonneg_left hcn (show 0 ≤ q * √N by positivity)
    nlinarith
  set a := |U - e w * D| with ha
  have ha0 : 0 ≤ a := abs_nonneg _
  have hNinv : N⁻¹ = (√N)⁻¹ * (√N)⁻¹ := by rw [← mul_inv, hsN]
  have hbound : √(n : ℝ) * |(U - e w * D) / D| ≤
      2 / (q * √c) * |√N * (N⁻¹ * (U - e w * D))| := by
    rw [abs_div, abs_of_pos hDpos, abs_mul, abs_mul, abs_of_pos hrpos,
      abs_of_pos (inv_pos.2 hNpos), ← ha, hNinv]
    calc √(n : ℝ) * (a / D) = (√(n : ℝ) * q * √c * √N) * a / (D * (q * √c * √N)) := by
          field_simp
      _ ≤ (2 * D) * a / (D * (q * √c * √N)) := by gcongr
      _ = 2 / (q * √c) * (√N * ((√N)⁻¹ * (√N)⁻¹ * a)) := by
          field_simp
  have := mul_lt_mul_of_pos_left hlt1 (show 0 < 2 / (q * √c) by positivity)
  rw [abs_of_nonneg (by positivity)] at hω
  linarith

/-- **The `√n` rate of the clipped cell proportion score.** For a finite covariate, an i.i.d.
sample with the law of the observed data, a correct score with values in `[ε', 1 - ε']`, every
cell `{W = w}` of positive probability and training sets with at least `c n` units for a
`c > 0`, `√n ‖ê_{n,k} - e‖₂` is bounded in probability, with `ê` the clipped cell proportion
score and `‖·‖₂` the `L²(P_W)` norm. -/
theorem boundedInProbabilityENNReal_sqrt_mul_fitError_clippedCellScore [Finite 𝒲]
    (hW : Measurable W) (hA : Measurable A) (hY : ∀ a, Measurable (Y a))
    (hps : IsPropensityScore μ A W e) {ε' : ℝ} (he : ∀ w, ε' ≤ e w ∧ e w ≤ 1 - ε')
    (hcell : ∀ w, 0 < μ.real (W ⁻¹' {w})) (hO : IsIIDSample O P)
    (hlaw : P.map (O 0) = μ.map (obsData A Y W)) (fold : ℕ → ℕ → Fin K) (k : Fin K) {c : ℝ}
    (hc : 0 < c) (htrain : ∀ᶠ n in atTop, c * n ≤ (cvTrain fold n k).card) :
    BoundedInProbabilityENNReal P (fun n ω => ENNReal.ofReal √(n : ℝ) *
      fitError (μ.map W) (fun t => clippedCellScore ε' t) e (trainingData fold O n k ω)) := by
  have := Fintype.ofFinite 𝒲
  have hsum := BoundedInProbability.finset_sum univ fun w _ =>
    boundedInProbability_sqrt_mul_cellPropFit_sub hW hA hY hps w (hcell w) hO hlaw fold k hc
      htrain
  rw [← boundedInProbabilityENNReal_ofReal_abs_iff] at hsum
  refine hsum.mono fun n ω => ?_
  set C := ∑ w, |cellPropFit (trainingData fold O n k ω) w - e w|
  have hC : 0 ≤ C := Finset.sum_nonneg fun w _ => abs_nonneg _
  have hle : fitError (μ.map W) (fun t => clippedCellScore ε' t) e (trainingData fold O n k ω) ≤
      ENNReal.ofReal C := by
    have hpt : ∀ w', ‖clippedCellScore ε' (trainingData fold O n k ω) w' - e w'‖ ≤ C :=
      fun w' => by
      rw [Real.norm_eq_abs]
      refine (abs_clipInterval_sub_le (he w').1 (he w').2).trans ?_
      exact Finset.single_le_sum (f := fun w =>
        |cellPropFit (trainingData fold O n k ω) w - e w|) (fun w _ => abs_nonneg _)
        (Finset.mem_univ w')
    have h := eLpNorm_le_of_ae_bound (p := 2) (μ := μ.map W)
      (f := fun w => clippedCellScore ε' (trainingData fold O n k ω) w - e w)
      (measurable_of_countable _).aestronglyMeasurable (C := C) (Eventually.of_forall hpt)
    simpa [fitError, measure_univ] using h
  calc ENNReal.ofReal √(n : ℝ) * fitError (μ.map W) (fun t => clippedCellScore ε' t) e
        (trainingData fold O n k ω) ≤ ENNReal.ofReal √(n : ℝ) * ENNReal.ofReal C := by gcongr
    _ = ENNReal.ofReal (√(n : ℝ) * C) := (ENNReal.ofReal_mul (Real.sqrt_nonneg _)).symm
    _ = ENNReal.ofReal (abs (∑ w, √(n : ℝ) *
          |cellPropFit (trainingData fold O n k ω) w - e w|)) := by
        rw [← Finset.mul_sum, abs_of_nonneg (by positivity)]

end CellProportion

/-! ### The randomized population with a fitted score -/

/-- The clipped cell proportion score with `ε' = 1/8`, as a learner of the parity folds. -/
noncomputable def twoPointScoreFit (n : ℕ) (k : Fin 2)
    (t : cvTrain parityFold n k → Bool × Bool × ℝ) (w : Bool) : ℝ :=
  clippedCellScore (1 / 8) t w

/-- Each parity fold has at least `⌊n / 2⌋` training units. -/
theorem card_cvTrain_parityFold_ge (n : ℕ) (k : Fin 2) :
    n / 2 ≤ (cvTrain parityFold n k).card := by
  have h := Finset.card_le_card_of_injOn (fun j => 2 * j + (1 - k.val)) (s := range (n / 2))
    (t := cvTrain parityFold n k) (fun j hj => ?_) (fun i _ j _ h => by simpa using h)
  · simpa using h
  have hk := k.isLt
  simp only [coe_range, Set.mem_Iio] at hj
  simp only [cvTrain, coe_filter, mem_range, Set.mem_ofPred_eq, parityFold, ne_eq,
    Fin.ext_iff]
  constructor <;> omega

/-- The parity folds have at least `n / 4` training units for `n ≥ 2`. -/
theorem eventually_card_cvTrain_parityFold (k : Fin 2) :
    ∀ᶠ n in atTop, (1 / 4 : ℝ) * n ≤ (cvTrain parityFold n k).card := by
  filter_upwards [eventually_ge_atTop 2] with n hn
  have h1 : n ≤ 2 * (n / 2) + 1 := by omega
  have h2 : (n : ℝ) ≤ 2 * ((n / 2 : ℕ) : ℝ) + 1 := by exact_mod_cast h1
  have h3 : ((n / 2 : ℕ) : ℝ) ≤ (cvTrain parityFold n k).card := by
    exact_mod_cast card_cvTrain_parityFold_ge n k
  have h4 : (2 : ℝ) ≤ n := by exact_mod_cast hn
  linarith

/-- Every covariate cell of the population has positive probability. -/
theorem twoPoint_covariate_cell_pos (w : Bool) :
    0 < twoPointLaw.real ((fun ω : Fin 3 → Bool => ω 0) ⁻¹' {w}) :=
  (twoPoint_cell_pos w true).trans_le (measureReal_mono fun ω hω =>
    (Prod.ext_iff.1 (show (ω 0, ω 1) = (w, true) from hω)).1)

/-- **The `√n` rate of the fitted score in the population.** -/
theorem boundedInProbabilityENNReal_twoPointScoreFit (k : Fin 2) :
    BoundedInProbabilityENNReal twoPointSampleLaw (fun n ω => ENNReal.ofReal √(n : ℝ) *
      fitError (twoPointLaw.map fun ω => ω 0) (twoPointScoreFit n k) (fun _ => 1 / 4)
        (trainingData parityFold twoPointSample n k ω)) :=
  boundedInProbabilityENNReal_sqrt_mul_fitError_clippedCellScore (measurable_coord 0)
    (measurable_coord 1) measurable_twoPointOutcome twoPoint_isPropensityScore
    (fun _ => by norm_num) twoPoint_covariate_cell_pos isIIDSample_twoPointSample
    (map_twoPointSample 0) parityFold k (by norm_num) (eventually_card_cvTrain_parityFold k)

theorem tendstoInMeasure_fitError_twoPointRegressionFit (k : Fin 2) (b : Bool) :
    TendstoInMeasure twoPointSampleLaw (fun n ω => fitError (twoPointLaw.map fun ω => ω 0)
      (fun t => twoPointRegressionFit n k t b) (twoPointRegression b)
        (trainingData parityFold twoPointSample n k ω)) atTop 0 :=
  tendstoInMeasure_fitError_cellMeanFit (measurable_coord 0) (measurable_coord 1)
    measurable_twoPointOutcome (fun _ => MemLp.of_discrete) twoPoint_isOutcomeRegression b
    (fun w => twoPoint_cell_pos w b) isIIDSample_twoPointSample (map_twoPointSample 0)
    parityFold k (tendsto_card_cvTrain_parityFold k)

/-- **The cross fitted estimator of `E[Y(1)]` with both nuisance functions fitted is
asymptotically normal with the efficient variance `5`.** The score is the clipped cell
proportion score and the regression the cell mean regression, both fitted on the other parity
fold; every hypothesis of `tendstoInDistribution_crossFitArm` is checked. -/
theorem tendstoInDistribution_crossFitArm_twoPoint_fittedScore {Ω'' : Type*}
    {mΩ'' : MeasurableSpace Ω''} {P'' : Measure Ω''} [IsProbabilityMeasure P''] {Z : Ω'' → ℝ}
    (hZ : HasLaw Z (gaussianReal 0 5) P'') :
    TendstoInDistribution (fun (n : ℕ) ω => √n * (crossFitArm parityFold twoPointScoreFit
      twoPointRegressionFit true twoPointSample n ω -
        armMean twoPointLaw twoPointOutcome true)) atTop Z (fun _ => twoPointSampleLaw) P'' := by
  have hpos := le_armProb_of_ae (twoPoint_strictOverlapAE.ae_comp
    (measurable_coord 0).aemeasurable)
  have hmi := twoPoint_ignorable.meanIgnorable (measurable_coord 0) (measurable_coord 1)
    measurable_twoPointOutcome true Integrable.of_finite
  have hAL := isAsymptoticallyLinear_crossFitArm parityFold (measurable_coord 0)
    (measurable_coord 1) measurable_twoPointOutcome (fun _ => MemLp.of_discrete)
    twoPoint_isPropensityScore twoPoint_isOutcomeRegression true hmi (by norm_num) (hpos true)
    isIIDSample_twoPointSample (map_twoPointSample 0)
    (fun _ _ => measurable_clippedCellScore _) (fun _ _ => measurable_cellMeanFit true)
    (ε' := 1 / 8) (by norm_num) (fun _ _ _ _ => clippedCellScore_mem (by norm_num) _ _)
    (fun k => tendstoInMeasure_of_bounded_sqrt_mul (boundedInProbabilityENNReal_twoPointScoreFit k))
    (fun k => tendstoInMeasure_fitError_twoPointRegressionFit k true)
    (fun k => tendstoInMeasure_sqrt_mul_mul_of_bounded_left
      (boundedInProbabilityENNReal_twoPointScoreFit k)
      (tendstoInMeasure_fitError_twoPointRegressionFit k true))
  have h5 : (∫ ω, armEIF (fun _ => 1 / 4) twoPointRegression true
      (armMean twoPointLaw twoPointOutcome true) (twoPointSample 0 ω) ^ 2
        ∂twoPointSampleLaw).toNNReal = 5 := by
    rw [integral_comp_obs (measurable_coord 0) (measurable_coord 1) measurable_twoPointOutcome
      (isIIDSample_twoPointSample.aemeasurable 0) (map_twoPointSample 0)
      ((measurable_armEIF measurable_const Measurable.of_discrete _).pow_const 2),
      twoPoint_integral_armEIF_sq]
    norm_num
  rw [← h5] at hZ
  exact hAL.tendstoInDistribution isIIDSample_twoPointSample
    (aemeasurable_crossFitArm parityFold (fun _ _ => measurable_clippedCellScore _)
      (fun _ _ => measurable_cellMeanFit true) isIIDSample_twoPointSample.aemeasurable) hZ

/-- **The cross fitted estimator of the average effect with both nuisance functions fitted is
asymptotically normal with the efficient variance `19/3`.** The score is the clipped cell
proportion score and the regression of both arms the cell mean regression, fitted on the other
parity fold; every hypothesis of `tendstoInDistribution_crossFitAte` is checked. -/
theorem tendstoInDistribution_crossFitAte_twoPoint_fittedScore {Ω'' : Type*}
    {mΩ'' : MeasurableSpace Ω''} {P'' : Measure Ω''} [IsProbabilityMeasure P''] {Z : Ω'' → ℝ}
    (hZ : HasLaw Z (gaussianReal 0 (19 / 3 : ℝ).toNNReal) P'') :
    TendstoInDistribution (fun (n : ℕ) ω => √n * (crossFitAte parityFold twoPointScoreFit
      twoPointRegressionFit twoPointSample n ω - ate twoPointLaw twoPointOutcome)) atTop Z
      (fun _ => twoPointSampleLaw) P'' := by
  have hmi : ∀ a, MeanIgnorable twoPointLaw (fun ω => ω 1) (fun ω => ω 0) twoPointOutcome a :=
    fun a => twoPoint_ignorable.meanIgnorable (measurable_coord 0) (measurable_coord 1)
      measurable_twoPointOutcome a Integrable.of_finite
  have hAL := isAsymptoticallyLinear_crossFitAte parityFold (measurable_coord 0)
    (measurable_coord 1) measurable_twoPointOutcome (fun _ => MemLp.of_discrete)
    twoPoint_isPropensityScore twoPoint_isOutcomeRegression hmi twoPoint_strictOverlapAE
    isIIDSample_twoPointSample (map_twoPointSample 0)
    (fun _ _ => measurable_clippedCellScore _) (fun _ _ b => measurable_cellMeanFit b)
    (ε' := 1 / 8) (by norm_num) (fun _ _ _ _ => clippedCellScore_mem (by norm_num) _ _)
    (fun k => tendstoInMeasure_of_bounded_sqrt_mul (boundedInProbabilityENNReal_twoPointScoreFit k))
    (fun k b => tendstoInMeasure_fitError_twoPointRegressionFit k b)
    (fun k b => tendstoInMeasure_sqrt_mul_mul_of_bounded_left
      (boundedInProbabilityENNReal_twoPointScoreFit k)
      (tendstoInMeasure_fitError_twoPointRegressionFit k b))
  have hvar : ∫ ω, ateEIF (fun _ => 1 / 4) twoPointRegression
      (ate twoPointLaw twoPointOutcome) (twoPointSample 0 ω) ^ 2 ∂twoPointSampleLaw =
        19 / 3 := by
    rw [integral_comp_obs (measurable_coord 0) (measurable_coord 1) measurable_twoPointOutcome
      (isIIDSample_twoPointSample.aemeasurable 0) (map_twoPointSample 0)
      ((measurable_ateEIF twoPoint_isPropensityScore.1 twoPoint_isOutcomeRegression.1
        _).pow_const 2)]
    exact twoPoint_integral_ateEIF_sq
  rw [← hvar] at hZ
  refine hAL.tendstoInDistribution isIIDSample_twoPointSample (fun n => ?_) hZ
  exact (aemeasurable_crossFitArm parityFold (fun _ _ => measurable_clippedCellScore _)
      (fun _ _ => measurable_cellMeanFit true) isIIDSample_twoPointSample.aemeasurable n).sub
    (aemeasurable_crossFitArm parityFold (fun _ _ => measurable_clippedCellScore _)
      (fun _ _ => measurable_cellMeanFit false) isIIDSample_twoPointSample.aemeasurable n)

end Efficiency
end CausalInference
