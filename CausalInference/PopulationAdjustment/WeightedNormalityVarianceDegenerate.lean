/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.PopulationAdjustment.WeightedNormalityWaldAnchored
public import CausalInference.PopulationAdjustment.WeightedNormalityExamples

/-!
# A vanishing asymptotic variance of the weighted arm mean

The asymptotic variance `σ² = E[IF²]` of `√n (m̂ₙ - m₀)` vanishes exactly when the influence
function vanishes almost surely. When the outcome is almost surely zero, the weighted arm mean
is zero for every sample, the influence function vanishes and the Wald interval
`[m̂ₙ ± z σ̂ₙ / √n]` contains `m₀ = 0` with probability one at every sample size. Its coverage
then tends to `1`, not to the nominal level `1 - α`: the positivity `0 < σ²` in the Wald
coverage theorem cannot be dropped.

The instance keeps every other hypothesis of the coverage theorem: the two coin model of
`WeightedConsistencyExamples` with the outcome replaced by `0`.

## Main definitions

* `zeroOutcome`: the record with its outcome replaced by `0`.
* `degenerateRecordLaw`: the law of the two coin records with outcome `0`.

## Main results

* `weightedArmVariance_eq_zero_iff`: `σ² = 0` if and only if `IF = 0` almost surely.
* `weightedArmVariance_eq_zero_of_outcome`: an almost surely zero outcome gives `σ² = 0`.
* `measureReal_weightedArm_waldInterval_of_outcome`: the coverage is `1` at every `n`.
* `not_tendsto_weightedArm_waldInterval_coverage_of_outcome`: the coverage does not tend to
  `1 - α` for `α ≠ 0`.
* `degenerate_margin`, `degenerate_prob_arm`, `degenerate_memLp_outcome`,
  `degenerate_weightedArmVariance`: the hypotheses of the coverage theorem except positivity.
* `exists_degenerate_not_tendsto_coverage`: a sample along which every hypothesis but `0 < σ²`
  holds and the coverage does not tend to `1 - α`.

## References

* Signorovitch, Wu, Yu, Gerrits, Kantor, Cai, Gupta, Mulani, *Comparative effectiveness without
  head-to-head trials* (2010).
* Stefanski, Boos, *The calculus of M-estimation* (2002).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Finset Matrix
open scoped Topology

namespace CausalInference

namespace PopulationAdjustment

open PointTreatment IndirectComparison

variable {𝒳 : Type*} {p : ℕ} [MeasurableSpace 𝒳] {ν : Measure (𝒳 × Bool × ℝ)}

/-- **The asymptotic variance vanishes exactly when the influence function vanishes almost
surely.** -/
theorem weightedArmVariance_eq_zero_iff [IsFiniteMeasure ν] {φ : 𝒳 → Fin p → ℝ}
    (hφ : Measurable φ) {t : Fin p → ℝ} {B : ℝ} (hB : ∀ x, ‖φ x - t‖ ≤ B) {δ : ℝ} (hδ : 0 < δ)
    (hmargin : ∀ v : Fin p → ℝ, ‖v‖ = 1 → δ ≤ ν.real {z | δ ≤ v ⬝ᵥ (φ z.1 - t)}) {a : Bool}
    (hq : 0 < ν.real {z | z.2.1 = a}) (hy : MemLp (fun z : 𝒳 × Bool × ℝ => z.2.2) 2 ν) :
    weightedArmVariance ν φ t a = 0 ↔ weightedArmInfluence ν φ t a =ᵐ[ν] 0 := by
  have hI : Integrable (fun z => weightedArmInfluence ν φ t a z ^ 2) ν := by
    have h := integrable_weightedArmInfluence_mul hφ hB hδ hmargin hq hq hy
    simpa only [sq] using h
  rw [weightedArmVariance, integral_eq_zero_iff_of_nonneg (fun z => sq_nonneg _) hI]
  constructor
  · intro h
    filter_upwards [h] with z hz
    simpa using hz
  · intro h
    filter_upwards [h] with z hz
    simp [hz]

section Outcome

variable {φ : 𝒳 → Fin p → ℝ} {t : Fin p → ℝ}

/-- An almost surely zero outcome has a zero tilted arm mean. -/
theorem tiltArmMean_eq_zero_of_outcome (hY : ∀ᵐ z ∂ν, z.2.2 = 0) (a : Bool)
    (β : Fin p → ℝ) : tiltArmMean ν φ t a β = 0 := by
  rw [tiltArmMean, integral_eq_zero_of_ae (hY.mono fun z hz => by simp [hz]), zero_div]

/-- An almost surely zero outcome has a zero coupling vector. -/
theorem weightedCoupling_eq_zero_of_outcome (hY : ∀ᵐ z ∂ν, z.2.2 = 0) (a : Bool) :
    weightedCoupling ν φ t a = 0 := by
  funext k
  exact integral_eq_zero_of_ae (hY.mono fun z hz => by
    simp [hz, tiltArmMean_eq_zero_of_outcome hY])

/-- An almost surely zero outcome has an almost surely zero influence function. -/
theorem weightedArmInfluence_ae_eq_zero_of_outcome (hY : ∀ᵐ z ∂ν, z.2.2 = 0) (a : Bool) :
    weightedArmInfluence ν φ t a =ᵐ[ν] 0 :=
  hY.mono fun z hz => by
    rw [Pi.zero_apply, weightedArmInfluence, hz, weightedCoupling_eq_zero_of_outcome hY,
      tiltArmMean_eq_zero_of_outcome hY]
    simp

/-- **An almost surely zero outcome has a zero asymptotic variance.** -/
theorem weightedArmVariance_eq_zero_of_outcome (hY : ∀ᵐ z ∂ν, z.2.2 = 0) (a : Bool) :
    weightedArmVariance ν φ t a = 0 :=
  integral_eq_zero_of_ae ((weightedArmInfluence_ae_eq_zero_of_outcome (φ := φ) (t := t) hY
    a).mono fun z hz => by
    simp only [Pi.zero_apply] at hz
    simp [hz])

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {O : ℕ → Ω → 𝒳 × Bool × ℝ}

/-- **The coverage is one at every sample size** when the outcome is almost surely zero: the
weighted arm mean is then `0 = m₀` for almost every sample. -/
theorem measureReal_weightedArm_waldInterval_of_outcome (hO : IsIIDSample O P)
    (hY : ∀ᵐ z ∂(P.map (O 0)), z.2.2 = 0) (a : Bool) {z : ℝ} (hz : 0 ≤ z) (n : ℕ) :
    P.real {ω | tiltArmMean (P.map (O 0)) φ t a (tiltMinimizer (P.map (O 0)) φ t) ∈
      waldInterval (sampleBalancedArmMean φ t O a n ω) (weightedArmSdHat φ t O a n ω) z n} =
      1 := by
  have h0 : ∀ᵐ ω ∂P, (O 0 ω).2.2 = 0 := ae_of_ae_map (hO.aemeasurable 0) hY
  have hall : ∀ᵐ ω ∂P, ∀ i, (O i ω).2.2 = 0 := ae_all_iff.2 fun i =>
    (hO.ident i).symm.ae_snd (p := fun r : 𝒳 × Bool × ℝ => r.2.2 = 0)
      (measurableSet_eq_fun measurable_snd.snd measurable_const) h0
  set S := {ω | tiltArmMean (P.map (O 0)) φ t a (tiltMinimizer (P.map (O 0)) φ t) ∈
      waldInterval (sampleBalancedArmMean φ t O a n ω) (weightedArmSdHat φ t O a n ω) z n}
  have hS : ∀ᵐ ω ∂P, ω ∈ S := hall.mono fun ω hω => by
    have hm : sampleBalancedArmMean φ t O a n ω = 0 := by
      simp [sampleBalancedArmMean, weightedArmMean, weightedMean, hω]
    have hsd : 0 ≤ z * weightedArmSdHat φ t O a n ω / √n :=
      div_nonneg (mul_nonneg hz (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _)
    simp only [S, Set.mem_ofPred_eq, waldInterval, hm, tiltArmMean_eq_zero_of_outcome hY,
      zero_sub, zero_add, Set.mem_Icc]
    exact ⟨neg_nonpos.2 hsd, hsd⟩
  have hc : P Sᶜ = 0 := ae_iff.1 hS
  have h1 : P S = 1 := by
    refine le_antisymm prob_le_one ?_
    have h := measure_univ_le_add_compl (μ := P) S
    rwa [measure_univ, hc, add_zero] at h
  rw [measureReal_def, h1, ENNReal.toReal_one]

/-- **Positivity is necessary for nominal coverage**: when the outcome is almost surely zero,
`σ² = 0` and the coverage of `[m̂ₙ ± z σ̂ₙ / √n]` tends to `1`, so it does not tend to `1 - α`
for any `α ≠ 0`. -/
theorem not_tendsto_weightedArm_waldInterval_coverage_of_outcome (hO : IsIIDSample O P)
    (hY : ∀ᵐ z ∂(P.map (O 0)), z.2.2 = 0) (a : Bool) {z α : ℝ} (hz : 0 ≤ z) (hα : α ≠ 0) :
    ¬ Tendsto (fun n => P.real {ω | tiltArmMean (P.map (O 0)) φ t a
      (tiltMinimizer (P.map (O 0)) φ t) ∈ waldInterval (sampleBalancedArmMean φ t O a n ω)
        (weightedArmSdHat φ t O a n ω) z n}) atTop (𝓝 (1 - α)) := by
  intro h
  have h1 : Tendsto (fun n => P.real {ω | tiltArmMean (P.map (O 0)) φ t a
      (tiltMinimizer (P.map (O 0)) φ t) ∈ waldInterval (sampleBalancedArmMean φ t O a n ω)
        (weightedArmSdHat φ t O a n ω) z n}) atTop (𝓝 1) := by
    simp_rw [measureReal_weightedArm_waldInterval_of_outcome hO hY a hz]
    exact tendsto_const_nhds
  have := tendsto_nhds_unique h h1
  exact hα (by linarith)

end Outcome

/-! ### The two coin model with a zero outcome -/

/-- The record with its outcome replaced by `0`. -/
def zeroOutcome (z : Bool × Bool × ℝ) : Bool × Bool × ℝ := (z.1, z.2.1, 0)

theorem measurable_zeroOutcome : Measurable zeroOutcome :=
  measurable_fst.prodMk (measurable_snd.fst.prodMk measurable_const)

/-- The law of the two coin records with outcome `0`: two independent fair coins `X`, `A` and
`Y = 0`. -/
noncomputable def degenerateRecordLaw : Measure (Bool × Bool × ℝ) :=
  exampleRecordLaw.map zeroOutcome

instance : IsProbabilityMeasure degenerateRecordLaw :=
  (Measure.isProbabilityMeasure_map_iff measurable_zeroOutcome.aemeasurable).2 inferInstance

/-- The sets of records that do not involve the outcome keep their probability. -/
theorem degenerateRecordLaw_real {S : Set (Bool × Bool × ℝ)} (hS : MeasurableSet S)
    (hSz : zeroOutcome ⁻¹' S = S) : degenerateRecordLaw.real S = exampleRecordLaw.real S := by
  rw [degenerateRecordLaw, map_measureReal_apply measurable_zeroOutcome hS, hSz]

/-- The outcome is almost surely zero. -/
theorem ae_degenerateRecordLaw_outcome : ∀ᵐ z ∂degenerateRecordLaw, z.2.2 = 0 :=
  (ae_map_iff measurable_zeroOutcome.aemeasurable
    (measurableSet_eq_fun measurable_snd.snd measurable_const)).2 (ae_of_all _ fun _ => rfl)

theorem degenerate_margin : ∀ v : Fin 1 → ℝ, ‖v‖ = 1 → (1 / 2 : ℝ) ≤
    degenerateRecordLaw.real {z | 1 / 2 ≤ v ⬝ᵥ (exampleFeature z.1 - exampleTarget)} := by
  intro v hv
  have hS : MeasurableSet {z : Bool × Bool × ℝ |
      1 / 2 ≤ v ⬝ᵥ (exampleFeature z.1 - exampleTarget)} :=
    measurableSet_le measurable_const
      ((measurable_of_countable fun x : Bool => v ⬝ᵥ (exampleFeature x - exampleTarget)).comp
        measurable_fst)
  rw [degenerateRecordLaw_real hS rfl]
  exact example_margin v hv

theorem degenerate_prob_arm (a : Bool) : degenerateRecordLaw.real {z | z.2.1 = a} = 1 / 2 := by
  rw [degenerateRecordLaw_real (measurableSet_eq_fun measurable_snd.fst measurable_const) rfl]
  exact example_prob_arm a

theorem degenerate_memLp_outcome :
    MemLp (fun z : Bool × Bool × ℝ => z.2.2) 2 degenerateRecordLaw :=
  MemLp.of_bound measurable_snd.snd.aestronglyMeasurable 0
    (ae_degenerateRecordLaw_outcome.mono fun z hz => by rw [hz, norm_zero])

/-- **The asymptotic variance vanishes** in both arms of the zero outcome model. -/
theorem degenerate_weightedArmVariance (a : Bool) :
    weightedArmVariance degenerateRecordLaw exampleFeature exampleTarget a = 0 :=
  weightedArmVariance_eq_zero_of_outcome ae_degenerateRecordLaw_outcome a

/-- **The positivity of the asymptotic variance cannot be dropped from the Wald coverage
theorem.** There is an i.i.d. sample whose record law satisfies the bound, the margin condition
with `δ = 1/2`, `P(A = a) = 1/2 > 0` and `E[Y²] < ∞`, has `σ² = 0`, and along which the coverage
of `[m̂ₙ ± z σ̂ₙ / √n]` does not tend to `1 - α`, for every `z ≥ 0` and `α ≠ 0`. -/
theorem exists_degenerate_not_tendsto_coverage (a : Bool) {z α : ℝ} (hz : 0 ≤ z)
    (hα : α ≠ 0) : ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω)
      (_ : IsProbabilityMeasure P) (O : ℕ → Ω → Bool × Bool × ℝ), IsIIDSample O P ∧
      P.map (O 0) = degenerateRecordLaw ∧
      weightedArmVariance (P.map (O 0)) exampleFeature exampleTarget a = 0 ∧
      ¬ Tendsto (fun n => P.real {ω | tiltArmMean (P.map (O 0)) exampleFeature exampleTarget a
        (tiltMinimizer (P.map (O 0)) exampleFeature exampleTarget) ∈
          waldInterval (sampleBalancedArmMean exampleFeature exampleTarget O a n ω)
            (weightedArmSdHat exampleFeature exampleTarget O a n ω) z n}) atTop
        (𝓝 (1 - α)) := by
  obtain ⟨Ω, _, P, O, hP, -, hO, hlaw⟩ := exists_isIIDSample degenerateRecordLaw
  have hl : P.map (O 0) = degenerateRecordLaw := (hlaw 0).map_eq
  refine ⟨Ω, _, P, hP, O, hO, hl, by rw [hl]; exact degenerate_weightedArmVariance a, ?_⟩
  exact not_tendsto_weightedArm_waldInterval_coverage_of_outcome hO
    (by rw [hl]; exact ae_degenerateRecordLaw_outcome) a hz hα

end PopulationAdjustment

end CausalInference
