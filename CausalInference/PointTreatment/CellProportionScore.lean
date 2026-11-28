/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.PointTreatment.AugmentedConsistency

/-!
# Point treatment: the cell proportion score for a finite covariate

For a covariate with finitely many values, the propensity score can be fitted cell by cell: the
fitted score at the value `w` is the proportion of treated units among the sampled units with
covariate `w`,
`ê n ξ w = (n⁻¹ ∑ 1{W_i = w, A_i = 1}) / (n⁻¹ ∑ 1{W_i = w})`,
with the fixed value `1 / 2` on an empty cell. If every cell has positive probability, the law
of large numbers for the numerator and the denominator, the ratio rule and a union over the
finitely many cells give uniform convergence in probability of `ê` to the propensity score
(`tendstoUniformlyOnInProbability_cellScore`), hence convergence on the sample
(`tendstoOnSample_cellScore`, through `TendstoOnSample.of_tendstoUniformlyOn`).

The limit is identified with any version `e` of the propensity score: on a cell of positive
probability, `E[1{A} 1{W = w}] = e(w) P(W = w)` by the defining property of the conditional
expectation. Positivity `0 < e(w) < 1` at every value gives strict positivity, the minimum over
the finitely many values (`exists_strictOverlap_of_finite`). So the fitted weighting and
augmented estimators with the cell score are consistent under ignorability with no further
hypothesis on the fit.

## Main definitions

* `cellIndObs`: the indicator `1{w' = w}` of a covariate cell at an observation.
* `cellScore`: the cell proportion score.

## Main results

* `WithProbTendingToOne.forall_finite`: a finite intersection of events with probability tending
  to one.
* `IsPropensityScore.setIntegral_respInd_cell`: `E[1{A} 1{W = w}] = e(w) P(W = w)`.
* `tendstoUniformlyOnInProbability_cellScore`, `tendstoOnSample_cellScore`.
* `exists_strictOverlap_of_finite`.
* `IndicatorIgnorable.isConsistent_sampleIpwAte_cellScore`,
  `Ignorable.isConsistent_sampleIpwAte_cellScore`: Horvitz and Thompson and Hájek.
* `IndicatorIgnorable.isConsistent_sampleAipwAte_cellScore`: the augmented estimator with the
  cell score and any fitted regression converging on the sample to an integrable limit.
-/

@[expose] public section

namespace CausalInference

open MeasureTheory ProbabilityTheory Filter

/-- **A finite intersection of events with probability tending to one** has probability tending
to one. -/
theorem WithProbTendingToOne.forall_finite {Ξ ι : Type*} {mΞ : MeasurableSpace Ξ}
    {P : Measure Ξ} [Finite ι] {S : ι → ℕ → Set Ξ} (h : ∀ j, WithProbTendingToOne P (S j)) :
    WithProbTendingToOne P (fun n => {ξ | ∀ j, ξ ∈ S j n}) := by
  classical
  have := Fintype.ofFinite ι
  have key : ∀ s : Finset ι, WithProbTendingToOne P (fun n => {ξ | ∀ j ∈ s, ξ ∈ S j n}) := by
    intro s
    induction s using Finset.induction_on with
    | empty => exact withProbTendingToOne_univ.mono fun n ξ _ j hj => absurd hj (by simp)
    | insert a s _ ih =>
      exact ((h a).inter ih).mono fun n ξ hξ j hj => by
        rcases Finset.mem_insert.1 hj with rfl | hj
        · exact hξ.1
        · exact hξ.2 j hj
  exact (key Finset.univ).mono fun n ξ hξ j => hξ j (Finset.mem_univ j)

namespace PointTreatment

open MissingData Finset

variable {Ω Ξ 𝒲 : Type*} {mΩ : MeasurableSpace Ω} {mΞ : MeasurableSpace Ξ} [MeasurableSpace 𝒲]
  {μ : Measure Ω} {P : Measure Ξ} {A : Ω → Bool} {W : Ω → 𝒲} {Y : Bool → Ω → ℝ} {e : 𝒲 → ℝ}
  {O : ℕ → Ξ → 𝒲 × Bool × ℝ}

/-- The indicator `1{w' = w}` of the covariate cell `w` at an observation `z = (w', b, y)`. -/
noncomputable def cellIndObs (w : 𝒲) : 𝒲 × Bool × ℝ → ℝ :=
  (Prod.fst ⁻¹' ({w} : Set 𝒲)).indicator 1

/-- **The cell proportion score**: the proportion of treated units among the sampled units with
covariate `w`, and `1 / 2` on an empty cell. -/
noncomputable def cellScore (O : ℕ → Ξ → 𝒲 × Bool × ℝ) (n : ℕ) (ξ : Ξ) (w : 𝒲) : ℝ :=
  if sampleMean (cellIndObs w) O n ξ = 0 then 1 / 2 else
    sampleMean (fun z => cellIndObs w z * armIndObs true z) O n ξ / sampleMean (cellIndObs w) O n ξ

theorem measurable_cellIndObs [MeasurableSingletonClass 𝒲] (w : 𝒲) :
    Measurable (cellIndObs w) :=
  measurable_const.indicator (measurable_fst (measurableSet_singleton w))

omit [MeasurableSpace 𝒲] in
theorem cellIndObs_comp (W : Ω → 𝒲) (A : Ω → Bool) (Y : Bool → Ω → ℝ) (w : 𝒲) (ω : Ω) :
    cellIndObs w (W ω, A ω, obsOutcome A Y ω) = (W ⁻¹' {w}).indicator 1 ω := by
  classical
  rw [cellIndObs, Set.indicator_apply, Set.indicator_apply]
  rfl

/-- **The propensity score on a cell**: `E[1{A} 1{W = w}] = e(w) P(W = w)`. -/
theorem IsPropensityScore.setIntegral_respInd_cell [IsFiniteMeasure μ]
    [MeasurableSingletonClass 𝒲] (hW : Measurable W) (hA : Measurable A)
    (hps : IsPropensityScore μ A W e) (w : 𝒲) :
    ∫ ω in W ⁻¹' {w}, respInd A ω ∂μ = e w * μ.real (W ⁻¹' {w}) := by
  have hs : MeasurableSet[MeasurableSpace.comap W inferInstance] (W ⁻¹' {w}) :=
    ⟨{w}, measurableSet_singleton w, rfl⟩
  rw [← setIntegral_condExp hW.comap_le (integrable_respInd hA) hs,
    setIntegral_congr_ae (hW (measurableSet_singleton w)) (hps.2.mono fun ω h _ => h),
    setIntegral_congr_fun (hW (measurableSet_singleton w)) (fun ω (hω : W ω = w) => by
      rw [hω]), setIntegral_const, smul_eq_mul, mul_comm]

/-- **The cell proportion score converges uniformly in probability to the propensity score**
when every cell has positive probability. -/
theorem tendstoUniformlyOnInProbability_cellScore [Finite 𝒲] [MeasurableSingletonClass 𝒲]
    [IsProbabilityMeasure P] [IsProbabilityMeasure μ] (hW : Measurable W) (hA : Measurable A)
    (hY : ∀ a, Measurable (Y a)) (hps : IsPropensityScore μ A W e)
    (hcell : ∀ w, 0 < μ.real (W ⁻¹' {w})) (hO : IsIIDSample O P)
    (hlaw : P.map (O 0) = μ.map fun ω => (W ω, A ω, obsOutcome A Y ω)) :
    TendstoUniformlyOnInProbability P (cellScore O) e Set.univ := by
  have hD : Measurable fun ω => (W ω, A ω, obsOutcome A Y ω) :=
    hW.prodMk (hA.prodMk (measurable_obsOutcome hA hY))
  intro δ hδ
  refine (WithProbTendingToOne.forall_finite (S := fun w n => {ξ | dist (cellScore O n ξ w) (e w)
    < δ}) fun w => ?_).mono fun n ξ hξ w _ => hξ w
  set q := μ.real (W ⁻¹' {w})
  have hind : ∀ ω, cellIndObs w (W ω, A ω, obsOutcome A Y ω) * armIndObs true
      (W ω, A ω, obsOutcome A Y ω) = (W ⁻¹' {w}).indicator (respInd A) ω := fun ω => by
    rw [cellIndObs_comp, armIndObs_comp, arm_true]
    by_cases h : W ω = w <;> simp [h]
  have hden : IsConsistent (sampleMean (cellIndObs w) O) q P := by
    have hint : Integrable (fun ω => cellIndObs w (W ω, A ω, obsOutcome A Y ω)) μ := by
      simp only [cellIndObs_comp]
      exact (integrable_const 1).indicator (hW (measurableSet_singleton w))
    have h := isConsistent_sampleMean_of_map_eq hO hD.aemeasurable hlaw (measurable_cellIndObs w)
      hint
    simp only [cellIndObs_comp] at h
    rwa [integral_indicator_one (hW (measurableSet_singleton w))] at h
  have hnum : IsConsistent (sampleMean (fun z => cellIndObs w z * armIndObs true z) O)
      (e w * q) P := by
    have hint : Integrable (fun ω => cellIndObs w (W ω, A ω, obsOutcome A Y ω) * armIndObs true
        (W ω, A ω, obsOutcome A Y ω)) μ := by
      simp only [hind]
      exact (integrable_respInd hA).indicator (hW (measurableSet_singleton w))
    have h := isConsistent_sampleMean_of_map_eq
      (f := fun z : 𝒲 × Bool × ℝ => cellIndObs w z * armIndObs true z) hO hD.aemeasurable hlaw
      ((measurable_cellIndObs w).mul (measurable_armIndObs true)) hint
    simp only [hind] at h
    rwa [integral_indicator (hW (measurableSet_singleton w)),
      hps.setIntegral_respInd_cell hW hA w] at h
  have hratio := hnum.div hden (hcell w).ne'
  rw [mul_div_cancel_right₀ _ (hcell w).ne'] at hratio
  refine ((hratio.withProbTendingToOne_dist_lt hδ).inter
    (hden.withProbTendingToOne_dist_lt (hcell w))).mono fun n ξ hξ => ?_
  obtain ⟨h1, h2⟩ := hξ
  simp only [Set.mem_ofPred_eq] at h1 h2 ⊢
  have hne : sampleMean (cellIndObs w) O n ξ ≠ 0 := by
    intro h0
    rw [h0, Real.dist_eq, zero_sub, abs_neg, abs_of_pos (hcell w)] at h2
    exact lt_irrefl _ h2
  simp only [cellScore, hne, ↓reduceIte]
  exact h1

/-- **The cell proportion score converges on the sample to the propensity score** when every
cell has positive probability. -/
theorem tendstoOnSample_cellScore [Finite 𝒲] [MeasurableSingletonClass 𝒲]
    [IsProbabilityMeasure P] [IsProbabilityMeasure μ] (hW : Measurable W) (hA : Measurable A)
    (hY : ∀ a, Measurable (Y a)) (hps : IsPropensityScore μ A W e)
    (hcell : ∀ w, 0 < μ.real (W ⁻¹' {w})) (hO : IsIIDSample O P)
    (hlaw : P.map (O 0) = μ.map fun ω => (W ω, A ω, obsOutcome A Y ω)) :
    TendstoOnSample P O (cellScore O) e :=
  TendstoOnSample.of_tendstoUniformlyOn hO
    (tendstoUniformlyOnInProbability_cellScore hW hA hY hps hcell hO hlaw)
    (Filter.Eventually.of_forall fun _ => Set.mem_univ _)

omit [MeasurableSpace 𝒲] in
/-- **Positivity at finitely many values is strict positivity.** -/
theorem exists_strictOverlap_of_finite [Finite 𝒲] [Nonempty 𝒲]
    (h : ∀ w, 0 < e w ∧ e w < 1) : ∃ ε, StrictOverlap e ε := by
  have := Fintype.ofFinite 𝒲
  obtain ⟨w₀, -, hw₀⟩ := Finset.exists_min_image Finset.univ (fun w => min (e w) (1 - e w))
    Finset.univ_nonempty
  refine ⟨min (e w₀) (1 - e w₀), lt_min (h w₀).1 (by linarith [(h w₀).2]), fun w => ?_⟩
  have hw := hw₀ w (Finset.mem_univ w)
  exact ⟨hw.trans (min_le_left _ _), by linarith [hw.trans (min_le_right _ _)]⟩

section Corollaries

variable [Finite 𝒲] [Nonempty 𝒲] [MeasurableSingletonClass 𝒲] [IsProbabilityMeasure P]
  [IsProbabilityMeasure μ]

/-- **Weighting with the cell proportion score.** For a finite covariate with positive cell
probabilities, under the indicator form of ignorability, positivity `0 < e(w) < 1` at every
value and integrable potential outcomes, the Horvitz and Thompson and the Hájek estimators of
the average effect with the cell proportion score are consistent for `E[Y(1) - Y(0)]`. -/
theorem IndicatorIgnorable.isConsistent_sampleIpwAte_cellScore (hW : Measurable W)
    (hA : Measurable A) (hY : ∀ a, Measurable (Y a)) (hYi : ∀ a, Integrable (Y a) μ)
    (hign : IndicatorIgnorable μ A W Y) (hps : IsPropensityScore μ A W e)
    (hpos : ∀ w, 0 < e w ∧ e w < 1) (hcell : ∀ w, 0 < μ.real (W ⁻¹' {w}))
    (hO : IsIIDSample O P) (hlaw : P.map (O 0) = μ.map fun ω => (W ω, A ω, obsOutcome A Y ω)) :
    IsConsistent (sampleIpwAte (cellScore O) O) (ate μ Y) P ∧
      IsConsistent (sampleHajekAte (cellScore O) O) (ate μ Y) P := by
  obtain ⟨ε, hε⟩ := exists_strictOverlap_of_finite hpos
  exact hign.isConsistent_sampleIpwAte_fitted hW hA hY hYi hps (hε.strictOverlapAE _) hO hlaw
    (tendstoOnSample_cellScore hW hA hY hps hcell hO hlaw)

/-- **Weighting with the cell proportion score under ignorability** `A ⫫ (Y(0), Y(1)) | W`. -/
theorem Ignorable.isConsistent_sampleIpwAte_cellScore [StandardBorelSpace Ω] (hW : Measurable W)
    (hA : Measurable A) (hY : ∀ a, Measurable (Y a)) (hYi : ∀ a, Integrable (Y a) μ)
    (hign : Ignorable μ A hW Y) (hps : IsPropensityScore μ A W e)
    (hpos : ∀ w, 0 < e w ∧ e w < 1) (hcell : ∀ w, 0 < μ.real (W ⁻¹' {w}))
    (hO : IsIIDSample O P) (hlaw : P.map (O 0) = μ.map fun ω => (W ω, A ω, obsOutcome A Y ω)) :
    IsConsistent (sampleIpwAte (cellScore O) O) (ate μ Y) P ∧
      IsConsistent (sampleHajekAte (cellScore O) O) (ate μ Y) P :=
  ((ignorable_iff_indicatorIgnorable hW hA hY).1 hign).isConsistent_sampleIpwAte_cellScore hW hA
    hY hYi hps hpos hcell hO hlaw

/-- **The augmented estimator with the cell proportion score.** For a finite covariate with
positive cell probabilities, under the indicator form of ignorability, positivity
`0 < e(w) < 1` at every value and integrable potential outcomes, the augmented estimator with
the cell proportion score and any fitted regression converging on the sample to a measurable
limit `m'` (correct or not) is consistent for `E[Y(1) - Y(0)]`. On a finite covariate `m'(a, W)`
is bounded, hence integrable. -/
theorem IndicatorIgnorable.isConsistent_sampleAipwAte_cellScore (hW : Measurable W)
    (hA : Measurable A) (hY : ∀ a, Measurable (Y a)) (hYi : ∀ a, Integrable (Y a) μ)
    (hign : IndicatorIgnorable μ A W Y) (hps : IsPropensityScore μ A W e)
    (hpos : ∀ w, 0 < e w ∧ e w < 1) (hcell : ∀ w, 0 < μ.real (W ⁻¹' {w}))
    (hO : IsIIDSample O P) (hlaw : P.map (O 0) = μ.map fun ω => (W ω, A ω, obsOutcome A Y ω))
    {m' : Bool → 𝒲 → ℝ} {mh : ℕ → Ξ → Bool → 𝒲 → ℝ}
    (hfm : ∀ a, TendstoOnSample P O (fun n ξ => mh n ξ a) (m' a)) :
    IsConsistent (sampleAipwAte (cellScore O) mh O) (ate μ Y) P := by
  obtain ⟨ε, hε⟩ := exists_strictOverlap_of_finite hpos
  have hov : OverlapAE e (μ.map W) := Filter.Eventually.of_forall hpos
  have hm' : ∀ a, Measurable (m' a) := fun _ => measurable_of_finite _
  have hm'i : ∀ a, Integrable (fun ω => m' a (W ω)) μ := fun a => by
    obtain ⟨C, hC⟩ := (Set.finite_range fun w => |m' a w|).bddAbove
    refine (integrable_const C).mono' ((hm' a).comp hW).aestronglyMeasurable
      (Filter.Eventually.of_forall fun ω => ?_)
    rw [Real.norm_eq_abs]
    exact hC (Set.mem_range_self (W ω))
  exact hign.isConsistent_sampleAipwAte_fitted hW hA hY hYi hps hov hps.1 hm'
    (hε.strictOverlapAE _) hm'i (Or.inl hps) hO hlaw
    (tendstoOnSample_cellScore hW hA hY hps hcell hO hlaw) hfm

end Corollaries

end PointTreatment

end CausalInference
