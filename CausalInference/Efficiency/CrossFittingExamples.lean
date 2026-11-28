/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.Efficiency.CrossFittingAverageEffect
public import CausalInference.Efficiency.BoundExamples
public import Mathlib.Probability.Independence.InfinitePi

/-!
# Cross fitting with cell means on a finite covariate

This file exercises the rate conditions of `CausalInference.Efficiency.CrossFittingNormality`
on a learner fitted from the training data.

**Means over growing sets of units.** For an i.i.d. sample and finite sets `S_n` of units with
`|S_n| → ∞`, the mean `|S_n|⁻¹ ∑_{i ∈ S_n} f(O_i)` of a square integrable `f(O_0)` is consistent
for `E f(O_0)` (`isConsistent_finsetMean`, by Chebyshev's inequality). The training units of a
fold are such sets as soon as the folds grow.

**The cell mean regression.** For a finite covariate the regression of the arm `b` is fitted
cell by cell on the training data: the fitted value at `w` is the mean outcome of the training
units with covariate `w` in the arm `b`, and `0` on an empty cell (`cellMeanFit`). It is jointly
measurable in the training data and the covariate (`measurable_cellMeanFit`), and when every cell
`{W = w, A = b}` has positive probability and the training sets grow, its out of fold `L²(P_W)`
error tends to `0` in probability (`tendstoInMeasure_fitError_cellMeanFit`): each cell value is
a ratio of two consistent means, and on a finite covariate the `L²` error is at most the sum of
the cell errors.

**The randomized population.** In the population of `CausalInference.Efficiency.BoundExamples`
(covariate `W` a fair coin, treatment with known probability `1/4`), the sample of i.i.d. copies
is an i.i.d. sample (`isIIDSample_twoPointSample`), the parity folds grow
(`tendsto_card_cvTrain_parityFold`), and with the known score `1/4` and the cell mean regression
every hypothesis of `tendstoInDistribution_crossFitArm` holds: the score error is identically
`0`, so the product condition is immediate, while the `L²` consistency of the fitted regression
is the theorem above. The cross fitted estimator of `E[Y(1)]` is asymptotically normal with the
efficient variance `5` (`tendstoInDistribution_crossFitArm_twoPoint`), and the cross fitted
estimator of the average effect with the efficient variance `19/3`
(`tendstoInDistribution_crossFitAte_twoPoint`).

## Main definitions

* `cellArmInd`, `cellMeanFit`: the cell indicator and the cell mean regression.
* `twoPointSample`, `parityFold`: the sample and the folds of the example.

## Main results

* `isConsistent_finsetMean`: consistency of means over growing sets of units.
* `IsOutcomeRegression.integral_cellArmInd_mul`: `E[1{W = w, A = b} Y] = m(b, w) P(W = w, A = b)`.
* `measurable_cellMeanFit`, `tendstoInMeasure_fitError_cellMeanFit`.
* `isIIDSample_twoPointSample`, `tendsto_card_cvTrain_parityFold`.
* `tendstoInDistribution_crossFitArm_twoPoint`, `tendstoInDistribution_crossFitAte_twoPoint`.

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

variable {Ω' 𝒪 : Type*} {mΩ' : MeasurableSpace Ω'} [MeasurableSpace 𝒪]
  {P : Measure Ω'} [IsProbabilityMeasure P]

/-! ### Means over growing sets of units -/

/-- **Consistency of means over growing sets of units.** For an i.i.d. sample, a measurable `f`
with `f(O_0)` square integrable and finite sets of units `S_n` with `|S_n| → ∞`, the mean
`|S_n|⁻¹ ∑_{i ∈ S_n} f(O_i)` is consistent for `E f(O_0)`: its variance is
`Var f(O_0) / |S_n|`, and Chebyshev's inequality applies. -/
theorem isConsistent_finsetMean {O : ℕ → Ω' → 𝒪} (hO : IsIIDSample O P) {f : 𝒪 → ℝ}
    (hf : Measurable f) (hf2 : MemLp (fun ω => f (O 0 ω)) 2 P) {S : ℕ → Finset ℕ}
    (hS : Tendsto (fun n => (S n).card) atTop atTop) :
    IsConsistent (fun n ω => ((S n).card : ℝ)⁻¹ * ∑ i ∈ S n, f (O i ω))
      (∫ ω, f (O 0 ω) ∂P) P := by
  rw [IsConsistent, tendstoInMeasure_iff_dist]
  intro η hη
  have hid := (hO.comp hf).ident
  have hi2 : ∀ i, MemLp (fun ω => f (O i ω)) 2 P := fun i => (hid i).memLp_iff.2 hf2
  have hmean : ∀ i, ∫ ω, f (O i ω) ∂P = ∫ ω, f (O 0 ω) ∂P := fun i => (hid i).integral_eq
  have hvar : ∀ i, Var[fun ω => f (O i ω); P] = Var[fun ω => f (O 0 ω); P] := fun i =>
    (hid i).variance_eq
  set σ2 := Var[fun ω => f (O 0 ω); P]
  have hbound : ∀ n, 1 ≤ (S n).card → P {ω | η ≤ dist (((S n).card : ℝ)⁻¹ *
      ∑ i ∈ S n, f (O i ω)) (∫ ω, f (O 0 ω) ∂P)} ≤
        ENNReal.ofReal (σ2 / ((S n).card * η ^ 2)) := by
    intro n hn
    have hN : (0 : ℝ) < (S n).card := by exact_mod_cast hn
    set X : Ω' → ℝ := fun ω => ((S n).card : ℝ)⁻¹ * ∑ i ∈ S n, f (O i ω) with hXdef
    have hX2 : MemLp X 2 P := (memLp_finsetSum (S n) fun i _ => hi2 i).const_mul _
    have hEX : ∫ ω, X ω ∂P = ∫ ω, f (O 0 ω) ∂P := by
      rw [hXdef, integral_const_mul, integral_finsetSum _ fun i _ =>
        (hi2 i).integrable one_le_two]
      simp only [hmean, Finset.sum_const, nsmul_eq_mul]
      field_simp
    have hVX : Var[X; P] = σ2 / (S n).card := by
      rw [hXdef, variance_const_mul, show (fun ω => ∑ i ∈ S n, f (O i ω)) =
          ∑ i ∈ S n, fun ω => f (O i ω) from (Finset.sum_fn _ _).symm,
        IndepFun.variance_sum (fun i _ => hi2 i) (fun i _ j _ hij =>
          hO.pairwise_indepFun hf hij)]
      simp only [hvar, Finset.sum_const, nsmul_eq_mul]
      field_simp
    refine (measure_mono fun ω hω => ?_).trans
      ((meas_ge_le_variance_div_sq hX2 hη).trans_eq (by rw [hVX, div_div]))
    simp only [Set.mem_ofPred_eq, Real.dist_eq] at hω ⊢
    rwa [hEX]
  have hlim : Tendsto (fun n => ENNReal.ofReal (σ2 / ((S n).card * η ^ 2))) atTop (𝓝 0) := by
    rw [← ENNReal.ofReal_zero]
    refine (ENNReal.continuous_ofReal.tendsto 0).comp ?_
    refine Tendsto.div_atTop tendsto_const_nhds ?_
    exact (tendsto_natCast_atTop_atTop.comp hS).atTop_mul_const (by positivity)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
    (Eventually.of_forall fun n => bot_le) ?_
  filter_upwards [hS.eventually_ge_atTop 1] with n hn
  exact hbound n hn

omit [IsProbabilityMeasure P] in
/-- The constant zero sequence in `ℝ≥0∞` converges in probability to `0`. -/
theorem tendstoInMeasure_zero_ennreal :
    TendstoInMeasure P (fun (_ : ℕ) (_ : Ω') => (0 : ℝ≥0∞)) atTop 0 := by
  intro ε hε
  simp [hε.ne']

/-! ### The cell mean regression -/

section CellMean

variable {𝒲 : Type*} [MeasurableSpace 𝒲] [DecidableEq 𝒲]

/-- The indicator `1{w' = w, t = b}` of the cell `(w, b)` at an observation `(w', t, y)`. -/
def cellArmInd (w : 𝒲) (b : Bool) (z : 𝒲 × Bool × ℝ) : ℝ := if z.1 = w ∧ z.2.1 = b then 1 else 0

/-- **The cell mean regression**: for training data `t : S → 𝒲 × Bool × ℝ`, the fitted value of
the arm `b` at the covariate value `w` is the mean outcome of the training units in the cell
`(w, b)`, and `0` on an empty cell. -/
noncomputable def cellMeanFit {S : Type*} [Fintype S] (t : S → 𝒲 × Bool × ℝ) (b : Bool)
    (w : 𝒲) : ℝ :=
  if ∑ i, cellArmInd w b (t i) = 0 then 0 else
    (∑ i, cellArmInd w b (t i) * (t i).2.2) / ∑ i, cellArmInd w b (t i)

theorem measurable_cellArmInd [MeasurableSingletonClass 𝒲] (w : 𝒲) (b : Bool) :
    Measurable (cellArmInd w b) := by
  have hs : MeasurableSet {z : 𝒲 × Bool × ℝ | z.1 = w ∧ z.2.1 = b} :=
    (measurable_fst (measurableSet_singleton w)).inter
      ((measurable_fst.comp measurable_snd) (measurableSet_singleton b))
  exact Measurable.ite hs measurable_const measurable_const

/-- The cell mean regression is jointly measurable in the training data and the covariate. -/
theorem measurable_cellMeanFit [Countable 𝒲] [MeasurableSingletonClass 𝒲] {S : Type*}
    [Fintype S] (b : Bool) :
    Measurable fun p : (S → 𝒲 × Bool × ℝ) × 𝒲 => cellMeanFit p.1 b p.2 := by
  refine measurable_from_prod_countable_left fun w => ?_
  have hN : Measurable fun t : S → 𝒲 × Bool × ℝ => ∑ i, cellArmInd w b (t i) :=
    Finset.measurable_sum _ fun i _ => (measurable_cellArmInd w b).comp (measurable_pi_apply i)
  have hY : Measurable fun t : S → 𝒲 × Bool × ℝ => ∑ i, cellArmInd w b (t i) * (t i).2.2 :=
    Finset.measurable_sum _ fun i _ => ((measurable_cellArmInd w b).comp
      (measurable_pi_apply i)).mul ((measurable_snd.comp measurable_snd).comp
        (measurable_pi_apply i))
  exact Measurable.ite (hN (measurableSet_singleton 0)) measurable_const (hY.div hN)

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {A : Ω → Bool} {Y : Bool → Ω → ℝ} {W : Ω → 𝒲}
  {m : Bool → 𝒲 → ℝ} {μ : Measure Ω} [IsProbabilityMeasure μ]

omit [MeasurableSpace 𝒲] [IsProbabilityMeasure μ] in
theorem cellArmInd_obsData (w : 𝒲) (b : Bool) (ω : Ω) :
    cellArmInd w b (obsData A Y W ω) =
      ((fun ω => (W ω, A ω)) ⁻¹' {(w, b)}).indicator 1 ω := by
  unfold cellArmInd obsData
  split_ifs with h
  · rw [Set.indicator_of_mem (by simpa using h)]; rfl
  · rw [Set.indicator_of_notMem (by simpa using h)]

/-- **The regression on a cell**: `E[1{W = w, A = b} Y] = m(b, w) P(W = w, A = b)`. -/
theorem IsOutcomeRegression.integral_cellArmInd_mul [MeasurableSingletonClass 𝒲]
    (hW : Measurable W) (hA : Measurable A) (hYi : ∀ a, Integrable (Y a) μ)
    (hreg : IsOutcomeRegression μ A W (obsOutcome A Y) m) (w : 𝒲) (b : Bool) :
    ∫ ω, cellArmInd w b (obsData A Y W ω) * (obsData A Y W ω).2.2 ∂μ =
      m b w * μ.real ((fun ω => (W ω, A ω)) ⁻¹' {(w, b)}) := by
  set s := (fun ω => (W ω, A ω)) ⁻¹' {(w, b)} with hsdef
  have hWA : Measurable fun ω => (W ω, A ω) := hW.prodMk hA
  have hsm : MeasurableSet s := hWA (measurableSet_singleton _)
  have hs : MeasurableSet[MeasurableSpace.comap (fun ω => (W ω, A ω)) inferInstance] s :=
    ⟨{(w, b)}, measurableSet_singleton _, rfl⟩
  have hYo := integrable_obsOutcome hA hYi
  have h1 : ∫ ω, cellArmInd w b (obsData A Y W ω) * (obsData A Y W ω).2.2 ∂μ =
      ∫ ω in s, obsOutcome A Y ω ∂μ := by
    rw [← integral_indicator hsm]
    refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
    change cellArmInd w b (obsData A Y W ω) * (obsData A Y W ω).2.2 = _
    rw [cellArmInd_obsData]
    by_cases hω : ω ∈ s
    · rw [Set.indicator_of_mem hω, Set.indicator_of_mem hω]; simp [obsData]
    · rw [Set.indicator_of_notMem hω, Set.indicator_of_notMem hω]; simp
  rw [h1, ← setIntegral_condExp hWA.comap_le hYo hs,
    setIntegral_congr_ae hsm (hreg.2.mono fun ω h _ => h),
    setIntegral_congr_fun hsm (fun ω (hω : (W ω, A ω) = (w, b)) => by
      simp only [Prod.mk.injEq] at hω; rw [hω.1, hω.2]), setIntegral_const, smul_eq_mul,
    mul_comm]

variable [Finite 𝒲] [MeasurableSingletonClass 𝒲] {K : ℕ} {O : ℕ → Ω' → 𝒲 × Bool × ℝ}

/-- **The cell mean regression is `L²` consistent out of fold.** For an i.i.d. sample with the
law of the observed data, square integrable potential outcomes, a correct regression `m`, every
cell `{W = w, A = b}` of positive probability and training sets of the fold `k` with
`|T_{n,k}| → ∞`, the out of fold `L²(P_W)` error of the cell mean regression of the arm `b`
tends to `0` in probability. -/
theorem tendstoInMeasure_fitError_cellMeanFit (hW : Measurable W) (hA : Measurable A)
    (hY : ∀ a, Measurable (Y a)) (hY2 : ∀ a, MemLp (Y a) 2 μ)
    (hreg : IsOutcomeRegression μ A W (obsOutcome A Y) m) (b : Bool)
    (hcell : ∀ w, 0 < μ.real ((fun ω => (W ω, A ω)) ⁻¹' {(w, b)})) (hO : IsIIDSample O P)
    (hlaw : P.map (O 0) = μ.map (obsData A Y W)) (fold : ℕ → ℕ → Fin K) (k : Fin K)
    (htrain : Tendsto (fun n => (cvTrain fold n k).card) atTop atTop) :
    TendstoInMeasure P (fun n ω => fitError (μ.map W) (fun t => cellMeanFit t b) (m b)
      (trainingData fold O n k ω)) atTop 0 := by
  have := Fintype.ofFinite 𝒲
  have hYi : ∀ a, Integrable (Y a) μ := fun a => (hY2 a).integrable one_le_two
  have hobs := measurable_obsData hW hA hY
  have hO0 := hO.aemeasurable 0
  -- the two cell means are consistent
  have hcons : ∀ w, IsConsistent (fun n ω => cellMeanFit (trainingData fold O n k ω) b w)
      (m b w) P := by
    intro w
    set g₁ : 𝒲 × Bool × ℝ → ℝ := fun z => cellArmInd w b z * z.2.2
    set g₂ : 𝒲 × Bool × ℝ → ℝ := cellArmInd w b
    have hg₂ : Measurable g₂ := measurable_cellArmInd w b
    have hg₁ : Measurable g₁ := hg₂.mul (measurable_snd.comp measurable_snd)
    have hg₂2 : MemLp (fun ω => g₂ (O 0 ω)) 2 P :=
      memLp_comp_obs hW hA hY hO0 hlaw hg₂ (MemLp.of_bound (hg₂.comp hobs).aestronglyMeasurable
        1 (Eventually.of_forall fun ω => by
          simp only [g₂, cellArmInd]; split_ifs <;> simp))
    have hg₁2 : MemLp (fun ω => g₁ (O 0 ω)) 2 P := by
      refine memLp_comp_obs hW hA hY hO0 hlaw hg₁ ?_
      refine (memLp_obsOutcome hA hY hY2).of_le_mul (c := 1)
        (hg₁.comp hobs).aestronglyMeasurable (Eventually.of_forall fun ω => ?_)
      simp only [g₁, cellArmInd, obsData]
      split_ifs <;> simp
    have h₁ := isConsistent_finsetMean hO hg₁ hg₁2 htrain
    have h₂ := isConsistent_finsetMean hO hg₂ hg₂2 htrain
    have hE₁ : ∫ ω, g₁ (O 0 ω) ∂P = m b w * μ.real ((fun ω => (W ω, A ω)) ⁻¹' {(w, b)}) := by
      rw [integral_comp_obs hW hA hY hO0 hlaw hg₁]
      exact IsOutcomeRegression.integral_cellArmInd_mul hW hA hYi hreg w b
    have hE₂ : ∫ ω, g₂ (O 0 ω) ∂P = μ.real ((fun ω => (W ω, A ω)) ⁻¹' {(w, b)}) := by
      rw [integral_comp_obs hW hA hY hO0 hlaw hg₂]
      rw [show (fun ω => g₂ (obsData A Y W ω)) = ((fun ω => (W ω, A ω)) ⁻¹' {(w, b)}).indicator 1
        from funext (cellArmInd_obsData w b),
        integral_indicator_one ((hW.prodMk hA) (measurableSet_singleton _))]
    rw [hE₁] at h₁
    rw [hE₂] at h₂
    have hq := IsConsistent.comp₂ (g := fun x y => x / y)
      (continuousAt_fst.div continuousAt_snd (hcell w).ne') h₁ h₂
    have hq' : IsConsistent (fun n ω =>
        (((cvTrain fold n k).card : ℝ)⁻¹ * ∑ i ∈ cvTrain fold n k, g₁ (O i ω)) /
          (((cvTrain fold n k).card : ℝ)⁻¹ * ∑ i ∈ cvTrain fold n k, g₂ (O i ω))) (m b w) P := by
      convert hq using 1
      exact (mul_div_cancel_right₀ _ (hcell w).ne').symm
    refine hq'.congr_left fun n => Eventually.of_forall fun ω => ?_
    simp only [cellMeanFit, trainingData, g₁, g₂]
    simp only [Finset.sum_coe_sort (cvTrain fold n k) (fun i => cellArmInd w b (O i ω)),
      Finset.sum_coe_sort (cvTrain fold n k) (fun i => cellArmInd w b (O i ω) * (O i ω).2.2)]
    split_ifs with h0
    · rw [h0, mul_zero, div_zero]
    · have hne : (cvTrain fold n k).Nonempty := by
        by_contra hem
        rw [Finset.not_nonempty_iff_eq_empty] at hem
        exact h0 (by rw [hem, Finset.sum_empty])
      have hc : ((cvTrain fold n k).card : ℝ)⁻¹ ≠ 0 :=
        inv_ne_zero (by exact_mod_cast hne.card_pos.ne')
      rw [mul_div_mul_left _ _ hc]
  -- the `L²` error is at most the sum of the cell errors
  have hsum : TendstoInMeasure P (fun n ω => ∑ w, |cellMeanFit (trainingData fold O n k ω) b w -
      m b w|) atTop 0 := by
    refine tendstoInMeasure_finset_sum univ fun w _ => ?_
    have h := hcons w
    rw [IsConsistent, tendstoInMeasure_iff_dist] at h
    rw [tendstoInMeasure_iff_dist]
    intro δ hδ
    simpa only [Real.dist_eq, sub_zero, abs_abs, Pi.zero_apply] using h δ hδ
  rw [tendstoInMeasure_zero_iff_ofReal]
  intro δ hδ
  rw [tendstoInMeasure_iff_norm] at hsum
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds (hsum δ hδ)
    (fun n => bot_le) fun n => measure_mono fun ω hω => ?_
  simp only [Set.mem_ofPred_eq, Pi.zero_apply, sub_zero] at hω ⊢
  set C := ∑ w, |cellMeanFit (trainingData fold O n k ω) b w - m b w|
  have hC : 0 ≤ C := Finset.sum_nonneg fun w _ => abs_nonneg _
  have hle : fitError (μ.map W) (fun t => cellMeanFit t b) (m b) (trainingData fold O n k ω) ≤
      ENNReal.ofReal C := by
    have hpt : ∀ w', ‖cellMeanFit (trainingData fold O n k ω) b w' - m b w'‖ ≤ C := fun w' => by
      rw [Real.norm_eq_abs]
      exact Finset.single_le_sum (f := fun w =>
        |cellMeanFit (trainingData fold O n k ω) b w - m b w|) (fun w _ => abs_nonneg _)
        (Finset.mem_univ w')
    have h := eLpNorm_le_of_ae_bound (p := 2) (μ := μ.map W)
      (f := fun w => cellMeanFit (trainingData fold O n k ω) b w - m b w)
      (measurable_of_countable _).aestronglyMeasurable (C := C) (Eventually.of_forall hpt)
    simpa [fitError, measure_univ] using h
  rw [Real.norm_eq_abs, abs_of_nonneg hC]
  exact (ENNReal.ofReal_le_ofReal_iff hC).1 (hω.trans hle)

end CellMean

/-! ### The randomized population -/

/-- An i.i.d. sample of the population: the law of infinitely many independent copies. -/
noncomputable def twoPointSampleLaw : Measure (ℕ → Fin 3 → Bool) :=
  Measure.infinitePi fun _ => twoPointLaw

instance : IsProbabilityMeasure twoPointSampleLaw := by
  unfold twoPointSampleLaw; infer_instance

/-- The observed data of the `i`th unit of the sample. -/
def twoPointSample (i : ℕ) (ω : ℕ → Fin 3 → Bool) : Bool × Bool × ℝ :=
  obsData (fun ω => ω 1) twoPointOutcome (fun ω => ω 0) (ω i)

/-- Two folds: the parity of the unit. -/
def parityFold (_ i : ℕ) : Fin 2 := ⟨i % 2, Nat.mod_lt _ (by norm_num)⟩

theorem measurable_twoPointObs :
    Measurable (obsData (fun ω : Fin 3 → Bool => ω 1) twoPointOutcome (fun ω => ω 0)) :=
  measurable_obsData (measurable_coord 0) (measurable_coord 1) measurable_twoPointOutcome

theorem map_twoPointSample (i : ℕ) : twoPointSampleLaw.map (twoPointSample i) =
    twoPointLaw.map (obsData (fun ω => ω 1) twoPointOutcome (fun ω => ω 0)) := by
  have : twoPointSample i = obsData (fun ω => ω 1) twoPointOutcome (fun ω => ω 0) ∘
      fun x : ℕ → Fin 3 → Bool => x i := rfl
  rw [this, ← Measure.map_map measurable_twoPointObs (measurable_pi_apply i), twoPointSampleLaw,
    Measure.infinitePi_map_eval]

/-- **The sample of the population is i.i.d.** -/
theorem isIIDSample_twoPointSample : IsIIDSample twoPointSample twoPointSampleLaw where
  indep := iIndepFun_infinitePi (P := fun _ => twoPointLaw) fun _ => measurable_twoPointObs
  ident i := ⟨(measurable_twoPointObs.comp (measurable_pi_apply i)).aemeasurable,
    (measurable_twoPointObs.comp (measurable_pi_apply 0)).aemeasurable,
    (map_twoPointSample i).trans (map_twoPointSample 0).symm⟩

/-- **The parity folds grow**: each has at least `⌊n / 2⌋` training units. -/
theorem tendsto_card_cvTrain_parityFold (k : Fin 2) :
    Tendsto (fun n => (cvTrain parityFold n k).card) atTop atTop := by
  have hle : ∀ n, n / 2 ≤ (cvTrain parityFold n k).card := fun n => by
    have h := Finset.card_le_card_of_injOn (fun j => 2 * j + (1 - k.val)) (s := range (n / 2))
      (t := cvTrain parityFold n k) (fun j hj => ?_) (fun i _ j _ h => by simpa using h)
    · simpa using h
    have hk := k.isLt
    simp only [coe_range, Set.mem_Iio] at hj
    simp only [cvTrain, coe_filter, mem_range, Set.mem_ofPred_eq, parityFold, ne_eq,
      Fin.ext_iff]
    constructor <;> omega
  exact tendsto_atTop_mono hle (Nat.tendsto_div_const_atTop (by norm_num))

/-- Every cell of the population has positive probability. -/
theorem twoPoint_cell_pos (w b : Bool) :
    0 < twoPointLaw.real ((fun ω : Fin 3 → Bool => (ω 0, ω 1)) ⁻¹' {(w, b)}) := by
  have hset : (fun ω : Fin 3 → Bool => (ω 0, ω 1)) ⁻¹' {(w, b)} =
      Set.univ.pi (fun i : Fin 3 => if i = 0 then {w} else if i = 1 then {b} else Set.univ) := by
    ext ω
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Prod.mk.injEq, Set.mem_pi,
      Set.mem_univ, true_imp_iff, Fin.forall_fin_succ]
    simp
  rw [measureReal_def, hset, twoPointLaw, Measure.pi_pi]
  refine ENNReal.toReal_pos ?_ (ENNReal.prod_ne_top fun i _ => measure_ne_top _ _)
  refine Finset.prod_ne_zero_iff.2 fun i _ => ?_
  fin_cases i <;> cases w <;> cases b <;> norm_num [twoPointCoin, boolLaw]

/-- The cell mean regression, as a learner of the folds. -/
noncomputable def twoPointRegressionFit (n : ℕ) (k : Fin 2)
    (t : cvTrain parityFold n k → Bool × Bool × ℝ) (b w : Bool) : ℝ :=
  cellMeanFit t b w

/-- **The cross fitted estimator of `E[Y(1)]` in the population is asymptotically normal with
the efficient variance `5`.** The score is the known constant `1/4` and the regression is the
cell mean regression fitted on the other fold; every hypothesis of
`tendstoInDistribution_crossFitArm` is checked, the `L²` consistency of the fitted regression by
`tendstoInMeasure_fitError_cellMeanFit`. -/
theorem tendstoInDistribution_crossFitArm_twoPoint {Ω'' : Type*} {mΩ'' : MeasurableSpace Ω''}
    {P'' : Measure Ω''} [IsProbabilityMeasure P''] {Z : Ω'' → ℝ}
    (hZ : HasLaw Z (gaussianReal 0 5) P'') :
    TendstoInDistribution (fun (n : ℕ) ω => √n * (crossFitArm parityFold
      (fun _ _ _ _ => 1 / 4) twoPointRegressionFit true twoPointSample n ω -
        armMean twoPointLaw twoPointOutcome true)) atTop Z (fun _ => twoPointSampleLaw) P'' := by
  have hpos := le_armProb_of_ae (twoPoint_strictOverlapAE.ae_comp
    (measurable_coord 0).aemeasurable)
  have hmi := twoPoint_ignorable.meanIgnorable (measurable_coord 0) (measurable_coord 1)
    measurable_twoPointOutcome true Integrable.of_finite
  have herrE : ∀ k : Fin 2, TendstoInMeasure twoPointSampleLaw (fun n ω =>
      fitError (twoPointLaw.map fun ω => ω 0) (fun (_ : cvTrain parityFold n k →
        Bool × Bool × ℝ) (_ : Bool) => (1 : ℝ) / 4) (fun _ => 1 / 4)
        (trainingData parityFold twoPointSample n k ω)) atTop 0 := fun k => by
    simp only [fitError, sub_self, eLpNorm_fun_zero]
    exact tendstoInMeasure_zero_ennreal
  have hAL := isAsymptoticallyLinear_crossFitArm parityFold (measurable_coord 0)
    (measurable_coord 1) measurable_twoPointOutcome (fun _ => MemLp.of_discrete)
    twoPoint_isPropensityScore twoPoint_isOutcomeRegression true hmi (by norm_num) (hpos true)
    isIIDSample_twoPointSample (map_twoPointSample 0) (fun _ _ => measurable_const)
    (fun _ _ => measurable_cellMeanFit true) (ε' := 1 / 4) (by norm_num)
    (fun _ _ _ _ => by norm_num) herrE
    (fun k => tendstoInMeasure_fitError_cellMeanFit (measurable_coord 0) (measurable_coord 1)
      measurable_twoPointOutcome (fun _ => MemLp.of_discrete) twoPoint_isOutcomeRegression true
      (fun w => twoPoint_cell_pos w true) isIIDSample_twoPointSample (map_twoPointSample 0)
      parityFold k (tendsto_card_cvTrain_parityFold k))
    (fun k => by
      simp only [fitError, sub_self, eLpNorm_fun_zero, zero_mul, mul_zero]
      exact tendstoInMeasure_zero_ennreal)
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
    (aemeasurable_crossFitArm parityFold (fun _ _ => measurable_const)
      (fun _ _ => measurable_cellMeanFit true) isIIDSample_twoPointSample.aemeasurable) hZ

/-- **The cross fitted estimator of the average effect in the randomized population** with the
known score `1/4` and the cell mean regression of both arms on the parity folds is
asymptotically normal with the efficient variance `19/3`. -/
theorem tendstoInDistribution_crossFitAte_twoPoint {Ω'' : Type*} {mΩ'' : MeasurableSpace Ω''}
    {P'' : Measure Ω''} [IsProbabilityMeasure P''] {Z : Ω'' → ℝ}
    (hZ : HasLaw Z (gaussianReal 0 (19 / 3 : ℝ).toNNReal) P'') :
    TendstoInDistribution (fun (n : ℕ) ω => √n * (crossFitAte parityFold
      (fun _ _ _ _ => 1 / 4) twoPointRegressionFit twoPointSample n ω -
        ate twoPointLaw twoPointOutcome)) atTop Z (fun _ => twoPointSampleLaw) P'' := by
  have hmi : ∀ a, MeanIgnorable twoPointLaw (fun ω => ω 1) (fun ω => ω 0) twoPointOutcome a :=
    fun a => twoPoint_ignorable.meanIgnorable (measurable_coord 0) (measurable_coord 1)
      measurable_twoPointOutcome a Integrable.of_finite
  have herrE : ∀ k : Fin 2, TendstoInMeasure twoPointSampleLaw (fun n ω =>
      fitError (twoPointLaw.map fun ω => ω 0) (fun (_ : cvTrain parityFold n k →
        Bool × Bool × ℝ) (_ : Bool) => (1 : ℝ) / 4) (fun _ => 1 / 4)
        (trainingData parityFold twoPointSample n k ω)) atTop 0 := fun k => by
    simp only [fitError, sub_self, eLpNorm_fun_zero]
    exact tendstoInMeasure_zero_ennreal
  have hAL := isAsymptoticallyLinear_crossFitAte parityFold (measurable_coord 0)
    (measurable_coord 1) measurable_twoPointOutcome (fun _ => MemLp.of_discrete)
    twoPoint_isPropensityScore twoPoint_isOutcomeRegression hmi twoPoint_strictOverlapAE
    isIIDSample_twoPointSample (map_twoPointSample 0) (fun _ _ => measurable_const)
    (fun _ _ b => measurable_cellMeanFit b) (ε' := 1 / 4) (by norm_num)
    (fun _ _ _ _ => by norm_num) herrE
    (fun k b => tendstoInMeasure_fitError_cellMeanFit (measurable_coord 0) (measurable_coord 1)
      measurable_twoPointOutcome (fun _ => MemLp.of_discrete) twoPoint_isOutcomeRegression b
      (fun w => twoPoint_cell_pos w b) isIIDSample_twoPointSample (map_twoPointSample 0)
      parityFold k (tendsto_card_cvTrain_parityFold k))
    (fun k b => by
      simp only [fitError, sub_self, eLpNorm_fun_zero, zero_mul, mul_zero]
      exact tendstoInMeasure_zero_ennreal)
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
  exact (aemeasurable_crossFitArm parityFold (fun _ _ => measurable_const)
      (fun _ _ => measurable_cellMeanFit true) isIIDSample_twoPointSample.aemeasurable n).sub
    (aemeasurable_crossFitArm parityFold (fun _ _ => measurable_const)
      (fun _ _ => measurable_cellMeanFit false) isIIDSample_twoPointSample.aemeasurable n)

end Efficiency
end CausalInference
