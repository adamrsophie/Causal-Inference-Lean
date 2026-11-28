/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.Estimation.BootstrapCoverage
public import CausalInference.NetworkMetaAnalysis.AggregationLimits

/-!
# Examples for the bootstrap limit theory

* **The fair coin.** For an i.i.d. sample of fair coin flips, scored `1` for heads and `0` for
  tails, the bootstrap percentile and basic intervals for the mean cover `1/2` with probability
  tending to `1 - α`: every hypothesis of `Bootstrap.tendsto_bootstrap_coverage_resampleMean` is
  discharged, the variance being `1/4` (`Bootstrap.coin_bootstrap_coverage`). Such samples exist
  (`Bootstrap.exists_coin_bootstrap_coverage`).
* **The degenerate case.** If the scored observations are constant, equal to `c`, then for every
  `n ≥ 1` the bootstrap law of the mean is the point mass at `c`, both intervals are `{c}`, and
  the coverage of `c` is `1`, not `1 - α` (`Bootstrap.percentileInterval_resampleMean_const`,
  `Bootstrap.tendsto_coverage_resampleMean_const`). This is the failure when `σ² = 0`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal

namespace CausalInference

namespace Bootstrap

open PosteriorLimit BiasAnalysis.Distributions NetworkMetaAnalysis

variable {Ω 𝒪 : Type*} {mΩ : MeasurableSpace Ω} [MeasurableSpace 𝒪]

/-! ### The fair coin -/

/-- The score of a coin flip: `1` for heads (`true`), `0` for tails. -/
def coinScore (b : Bool) : ℝ := if b then 1 else 0

theorem measurable_coinScore : Measurable coinScore := measurable_of_countable _

/-- **Bootstrap coverage for the mean of a fair coin.** For an i.i.d. sample `O` of fair coin
flips (each with law `bernoulliLaw (1/2)`), `α ∈ (0, 1)` and `Φ(z) = 1 - α/2`, the bootstrap
percentile and basic intervals for the mean score cover the true mean `1/2` with probability
tending to `1 - α`. -/
theorem coin_bootstrap_coverage {P : Measure Ω} [IsProbabilityMeasure P] {O : ℕ → Ω → Bool}
    (hO : IsIIDSample O P) (hlaw : HasLaw (O 0) (bernoulliLaw (1 / 2)) P) {α z : ℝ}
    (hα : α ∈ Ioo (0 : ℝ) 1) (hz : cdf (gaussianReal 0 1) z = 1 - α / 2) :
    Tendsto (fun n ↦ P.real {ω | (1 / 2 : ℝ) ∈
        percentileInterval (bootstrapLaw (resampleMean coinScore) O n ω) α}) atTop
        (𝓝 (1 - α)) ∧
      Tendsto (fun n ↦ P.real {ω | (1 / 2 : ℝ) ∈
        basicInterval (bootstrapLaw (resampleMean coinScore) O n ω)
          (sampleMean coinScore O n ω) α}) atTop (𝓝 (1 - α)) := by
  have hb : IsProbabilityMeasure (bernoulliLaw (1 / 2)) :=
    isProbabilityMeasure_bernoulliLaw (by norm_num) (by norm_num)
  have hm : AEMeasurable (fun ω ↦ coinScore (O 0 ω)) P :=
    measurable_coinScore.comp_aemeasurable hlaw.aemeasurable
  have hf2 : MemLp (fun ω ↦ coinScore (O 0 ω)) 2 P :=
    MemLp.of_bound hm.aestronglyMeasurable 1 (ae_of_all _ fun ω ↦ by
      unfold coinScore; split_ifs <;> simp)
  have hint : ∀ g : Bool → ℝ, P[fun ω ↦ g (O 0 ω)] = (1 - 1 / 2) * g false + 1 / 2 * g true :=
    fun g ↦ by
      rw [← integral_bernoulliLaw (by norm_num) (by norm_num) g]
      exact hlaw.integral_comp (measurable_of_countable g).aestronglyMeasurable
  have hmean : P[fun ω ↦ coinScore (O 0 ω)] = 1 / 2 := by
    rw [hint]; simp [coinScore]
  have hvar : Var[fun ω ↦ coinScore (O 0 ω); P] = 1 / 4 := by
    rw [variance_eq_sub hf2]
    have h2 : P[(fun ω ↦ coinScore (O 0 ω)) ^ 2] = 1 / 2 := by
      have := hint (fun b ↦ coinScore b ^ 2)
      simp only [Pi.pow_apply]
      rw [this]; simp [coinScore]
    rw [h2, hmean]
    norm_num
  have h := tendsto_bootstrap_coverage_resampleMean hO measurable_coinScore hf2
    (by rw [hvar]; norm_num) hα hz
  rw [hmean] at h
  exact h

/-- **The coin example is not vacuous.** There is a probability space carrying an i.i.d. sample
of fair coin flips, and on it the bootstrap percentile interval for the mean score covers `1/2`
with probability tending to `1 - α`. -/
theorem exists_coin_bootstrap_coverage {α z : ℝ} (hα : α ∈ Ioo (0 : ℝ) 1)
    (hz : cdf (gaussianReal 0 1) z = 1 - α / 2) :
    ∃ Ω : Type, ∃ _ : MeasurableSpace Ω, ∃ P : Measure Ω, ∃ O : ℕ → Ω → Bool,
      IsProbabilityMeasure P ∧ IsIIDSample O P ∧ HasLaw (O 0) (bernoulliLaw (1 / 2)) P ∧
        Tendsto (fun n ↦ P.real {ω | (1 / 2 : ℝ) ∈
          percentileInterval (bootstrapLaw (resampleMean coinScore) O n ω) α}) atTop
          (𝓝 (1 - α)) := by
  have hb : IsProbabilityMeasure (bernoulliLaw (1 / 2)) :=
    isProbabilityMeasure_bernoulliLaw (by norm_num) (by norm_num)
  obtain ⟨Ω, mΩ, P, O, hP, -, hO, hlaw⟩ := exists_isIIDSample (bernoulliLaw (1 / 2))
  exact ⟨Ω, mΩ, P, O, hP, hO, hlaw 0, (coin_bootstrap_coverage hO (hlaw 0) hα hz).1⟩

/-! ### The degenerate case -/

/-- The quantile of a point mass at `c` at any level `u ∈ (0, 1)` is `c`. -/
theorem quantile_dirac (c : ℝ) {u : ℝ} (hu : u ∈ Ioo (0 : ℝ) 1) :
    quantile (Measure.dirac c) u = c := by
  have hcdf : ∀ x, cdf (Measure.dirac c) x = (Iic x).indicator 1 c := fun x ↦ by
    rw [cdf_eq_real, measureReal_def, Measure.dirac_apply' _ measurableSet_Iic]
    by_cases h : c ∈ Iic x <;> simp [h]
  refine le_antisymm ((quantile_le_iff hu c).2 ?_) (le_of_not_gt fun hlt ↦ ?_)
  · rw [hcdf]; simp [hu.2.le]
  · have h := (quantile_le_iff hu (quantile (Measure.dirac c) u)).1 le_rfl
    rw [hcdf, Set.indicator_of_notMem (by simpa using hlt)] at h
    exact absurd h (not_le.2 hu.1)

/-- **Constant data.** If every observation scores `c` (`f (O k ω) = c` for all `k`, `ω`), then
for `n ≥ 1` the bootstrap law of the resample mean is the point mass at `c`, and both bootstrap
intervals at a level `α ∈ (0, 1)` are `{c}`. -/
theorem percentileInterval_resampleMean_const {O : ℕ → Ω → 𝒪} {f : 𝒪 → ℝ} (hf : Measurable f)
    {c : ℝ} (hc : ∀ k ω, f (O k ω) = c) {n : ℕ} (hn : 1 ≤ n) (ω : Ω) {α : ℝ}
    (hα : α ∈ Ioo (0 : ℝ) 1) :
    bootstrapLaw (resampleMean f) O n ω = Measure.dirac c ∧
      percentileInterval (bootstrapLaw (resampleMean f) O n ω) α = {c} ∧
      basicInterval (bootstrapLaw (resampleMean f) O n ω) (sampleMean f O n ω) α = {c} := by
  have hn0 : (n : ℝ) ≠ 0 := by positivity
  have hlaw : bootstrapLaw (resampleMean f) O n ω = Measure.dirac c := by
    rw [bootstrapLaw, resampleLaw, Measure.map_map (measurable_resampleMean hf n)
      (measurable_resample O n ω)]
    have : resampleMean f n ∘ resample O n ω = fun _ ↦ c := by
      funext κ
      simp only [Function.comp_apply, resampleMean, resample, hc, Finset.sum_const,
        Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      field_simp
    rw [this, Measure.map_const, measure_univ, one_smul]
  have hxb : sampleMean f O n ω = c := by
    simp only [sampleMean, hc, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    field_simp
  have hlo : α / 2 ∈ Ioo (0 : ℝ) 1 := ⟨by linarith [hα.1], by linarith [hα.2]⟩
  have hhi : 1 - α / 2 ∈ Ioo (0 : ℝ) 1 := ⟨by linarith [hα.2], by linarith [hα.1]⟩
  refine ⟨hlaw, ?_, ?_⟩
  · rw [percentileInterval, hlaw, quantile_dirac c hlo, quantile_dirac c hhi, Icc_self]
  · rw [basicInterval, hlaw, quantile_dirac c hlo, quantile_dirac c hhi, hxb,
      show 2 * c - c = c by ring, Icc_self]

/-- **The coverage is `1` when the variance is `0`.** For constant scored data the bootstrap
percentile and basic intervals contain `c` for every `n ≥ 1`, so their coverage tends to `1`,
not to `1 - α`: the hypothesis `σ² > 0` of the coverage theorems cannot be dropped. -/
theorem tendsto_coverage_resampleMean_const {P : Measure Ω} [IsProbabilityMeasure P]
    {O : ℕ → Ω → 𝒪} {f : 𝒪 → ℝ} (hf : Measurable f) {c : ℝ}
    (hc : ∀ k ω, f (O k ω) = c) {α : ℝ} (hα : α ∈ Ioo (0 : ℝ) 1) :
    Tendsto (fun n ↦ P.real {ω | c ∈
        percentileInterval (bootstrapLaw (resampleMean f) O n ω) α}) atTop (𝓝 1) ∧
      Tendsto (fun n ↦ P.real {ω | c ∈
        basicInterval (bootstrapLaw (resampleMean f) O n ω) (sampleMean f O n ω) α}) atTop
        (𝓝 1) := by
  constructor <;> refine tendsto_const_nhds.congr' ((eventually_ge_atTop 1).mono fun n hn ↦ ?_)
  · have : {ω | c ∈ percentileInterval (bootstrapLaw (resampleMean f) O n ω) α} = univ := by
      ext ω
      simp [(percentileInterval_resampleMean_const hf hc hn ω hα).2.1]
    beta_reduce
    rw [this, probReal_univ]
  · have : {ω | c ∈ basicInterval (bootstrapLaw (resampleMean f) O n ω)
        (sampleMean f O n ω) α} = univ := by
      ext ω
      simp [(percentileInterval_resampleMean_const hf hc hn ω hα).2.2]
    beta_reduce
    rw [this, probReal_univ]

end Bootstrap

end CausalInference
