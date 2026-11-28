/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.PopulationAdjustment.WeightedBootstrapCoverage
public import CausalInference.PopulationAdjustment.WeightedNormalityVarianceZero

/-!
# An instance of the bootstrap coverage of the weighted arm mean

The record law is that of `(X, true, 1{X})` for a fair coin `X`: every unit is in the treated
arm and the outcome is `1{X}`. With no matched feature (`p = 0`, `φ = 0`, `t = 0`) the
entropy balancing weights are uniform, the bounded feature and margin conditions hold trivially,
the weighted arm mean is the sample mean of the outcome, and every hypothesis of
`tendsto_bootstrapArmMean_coverage` is verified. Here bootstrap linearity also has a direct
proof: the bootstrap remainder vanishes on the support of the resampling law for almost every
data path (`zeroFeature_isBootstrapLinear`). The weighted arm mean is `m₀ = 1/2` and the
variance is `σ² = 1/4`.

## Main definitions

* `zeroFeature`: the feature with no coordinates.

## Main results

* `zeroFeature_weightedArmInfluence`: `IF(z) = 1{A = true} (Y - 1/2)`.
* `zeroFeature_weightedArmVariance`: `σ² = 1/4`.
* `zeroFeature_isBootstrapLinear`: bootstrap linearity of the weighted arm mean.
* `zeroFeature_bootstrap_coverage`: percentile and basic coverage `1 - α`.
* `zeroFeature_unanchored_bootstrap_coverage`: the same for the unanchored comparison.
* `exists_zeroFeature_bootstrap_coverage`: the instance is not vacuous.

## References

* B. Efron (1979), *Bootstrap methods: another look at the jackknife*, Annals of Statistics 7.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Finset Matrix Set
open scoped Topology ENNReal

namespace CausalInference

namespace PopulationAdjustment

open PointTreatment Bootstrap IndirectComparison

/-- The feature with no coordinates. -/
def zeroFeature (_ : Bool) : Fin 0 → ℝ := 0

theorem measurable_zeroFeature : Measurable zeroFeature := measurable_const

/-- With no coordinates the tilt `exp(α + βᵀ(φ(x) - c))` is `exp α`. -/
theorem tiltWeight_zeroFeature (c : Fin 0 → ℝ) (α : ℝ) (β : Fin 0 → ℝ) (x : Bool) :
    tiltWeight zeroFeature c α β x = Real.exp α := by
  simp [tiltWeight, dotProduct]

/-- The indicator of an arm is measurable. -/
theorem measurable_armIndObs (a : Bool) :
    Measurable fun z : Bool × Bool × ℝ => armIndObs a z :=
  (measurable_of_countable fun b : Bool => if b = a then (1 : ℝ) else 0).comp measurable_snd.fst

/-- Integrals under the one arm record law: the average over the two coin values. -/
theorem integral_oneArmRecordLaw {f : Bool × Bool × ℝ → ℝ} (hf : Measurable f) :
    ∫ z, f z ∂oneArmRecordLaw = (f (true, true, 1) + f (false, true, 0)) / 2 := by
  rw [oneArmRecordLaw, integral_map measurable_oneArmRecord.aemeasurable hf.aestronglyMeasurable,
    integral_exampleRecordLaw]
  simp only [oneArmRecord, exampleRecord, exampleInd]
  norm_num
  ring

theorem zeroFeature_weightedArmMass :
    weightedArmMass oneArmRecordLaw zeroFeature 0 true = 1 := by
  rw [weightedArmMass]
  simp only [tiltWeight_zeroFeature, Real.exp_zero, mul_one]
  rw [integral_oneArmRecordLaw (measurable_armIndObs true)]
  norm_num [armIndObs]

theorem zeroFeature_tiltArmMean (β : Fin 0 → ℝ) :
    tiltArmMean oneArmRecordLaw zeroFeature 0 true β = 1 / 2 := by
  rw [tiltArmMean]
  simp only [tiltWeight_zeroFeature, Real.exp_zero, mul_one]
  rw [integral_oneArmRecordLaw (measurable_armIndObs true),
    integral_oneArmRecordLaw (f := fun z => armIndObs true z * z.2.2)
      ((measurable_armIndObs true).mul measurable_snd.snd)]
  norm_num [armIndObs]

/-- **The influence function without matching**: `IF(z) = 1{A = true} (Y - 1/2)`. -/
theorem zeroFeature_weightedArmInfluence :
    weightedArmInfluence oneArmRecordLaw zeroFeature 0 true =
      fun z => armIndObs true z * (z.2.2 - 1 / 2) := by
  funext z
  rw [weightedArmInfluence, zeroFeature_weightedArmMass, zeroFeature_tiltArmMean]
  simp [tiltWeight_zeroFeature, dotProduct]

/-- **The variance without matching** is the variance `1/4` of the fair coin outcome. -/
theorem zeroFeature_weightedArmVariance :
    weightedArmVariance oneArmRecordLaw zeroFeature 0 true = 1 / 4 := by
  rw [weightedArmVariance, zeroFeature_weightedArmInfluence]
  rw [integral_oneArmRecordLaw (f := fun z => (armIndObs true z * (z.2.2 - 1 / 2)) ^ 2)
    (((measurable_armIndObs true).mul (measurable_snd.snd.sub_const _)).pow_const 2)]
  norm_num [armIndObs]

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {O : ℕ → Ω → Bool × Bool × ℝ}

/-- On a sample of treated records the statistic is the mean of the outcome. -/
theorem bootstrapArmMean_zeroFeature {n : ℕ} {y : Fin n → Bool × Bool × ℝ}
    (hy : ∀ i, (y i).2.1 = true) :
    bootstrapArmMean zeroFeature 0 true n y = resampleMean (fun z => z.2.2) n y := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [bootstrapArmMean, weightedArmMean, weightedMean, resampleMean]
  rw [bootstrapArmMean_eq_div]
  have hn' : (n : ℝ) ≠ 0 := by positivity
  simp only [resampleMean, tiltWeight_zeroFeature, Real.exp_zero, mul_one, armIndObs, hy,
    ite_true, one_mul, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  field_simp

omit [IsProbabilityMeasure P] in
/-- **Bootstrap linearity without matching.** For an i.i.d. sample of the one arm record law,
the bootstrap remainder of the weighted arm mean vanishes on the support of the resampling law
for almost every data path; in particular it is small in conditional probability. -/
theorem zeroFeature_isBootstrapLinear (hO : IsIIDSample O P)
    (hlaw : P.map (O 0) = oneArmRecordLaw) :
    IsBootstrapLinear P O (bootstrapArmMean zeroFeature 0 true)
      (weightedArmInfluence (P.map (O 0)) zeroFeature 0 true) := by
  rw [hlaw, zeroFeature_weightedArmInfluence]
  have hgood : ∀ᵐ ω ∂P, ∀ k, (O k ω).2.1 = true := by
    refine ae_all_iff.2 fun k =>
    ae_of_ae_map (p := fun z : Bool × Bool × ℝ => z.2.1 = true) (hO.aemeasurable k) ?_
    rw [(hO.ident k).map_eq, hlaw]
    exact ae_oneArmRecordLaw_arm
  intro ρ hρ
  rw [tendstoInMeasure_iff_dist]
  intro ε hε
  refine tendsto_const_nhds.congr fun n => (measure_mono_null (fun ω hω => ?_)
    (ae_iff.1 hgood)).symm
  simp only [Set.mem_ofPred_eq] at hω ⊢
  intro hall
  refine absurd hω (not_le.2 ?_)
  set G : Set (Fin n → Bool × Bool × ℝ) := {y | ∀ i, (y i).2.1 = true} with hG
  have hGm : MeasurableSet G := by
    rw [hG, Set.ofPred_forall]
    exact MeasurableSet.iInter fun i =>
      measurableSet_eq_fun (measurable_pi_apply i).snd.fst measurable_const
  have hsub : {y | ρ ≤ |bootstrapRemainder (bootstrapArmMean zeroFeature 0 true)
      (fun z => armIndObs true z * (z.2.2 - 1 / 2)) O n ω y|} ⊆ Gᶜ := by
    intro y hy hyG
    simp only [Set.mem_ofPred_eq] at hy
    have hd : ∀ i, (dataPrefix O n ω i).2.1 = true := fun i => hall i
    have hyG' : ∀ i, (y i).2.1 = true := hyG
    have hR : bootstrapRemainder (bootstrapArmMean zeroFeature 0 true)
        (fun z => armIndObs true z * (z.2.2 - 1 / 2)) O n ω y = 0 := by
      have hsm : sampleMean (fun z => armIndObs true z * (z.2.2 - 1 / 2)) O n ω =
          resampleMean (fun z => armIndObs true z * (z.2.2 - 1 / 2)) n (dataPrefix O n ω) :=
        sampleMean_eq_resampleMean_dataPrefix _ O n ω
      rw [bootstrapRemainder, bootstrapArmMean_zeroFeature hyG', bootstrapArmMean_zeroFeature hd,
        hsm]
      simp only [resampleMean, armIndObs, hyG', hd, ite_true, one_mul, Finset.sum_sub_distrib]
      ring
    rw [hR, abs_zero] at hy
    linarith
  have h0 : (resampleLaw O n ω) Gᶜ = 0 := by
    rw [resampleLaw, Measure.map_apply (measurable_resample O n ω) hGm.compl]
    convert measure_empty (μ := resampleIndexLaw n)
    ext κ
    simp [resample, hG, hall]
  have : (resampleLaw O n ω).real {y | ρ ≤ |bootstrapRemainder
      (bootstrapArmMean zeroFeature 0 true) (fun z => armIndObs true z * (z.2.2 - 1 / 2))
        O n ω y|} = 0 := by
    rw [measureReal_def, measure_mono_null hsub h0, ENNReal.toReal_zero]
  rw [this, dist_self]
  exact hε

omit [IsProbabilityMeasure P] in
/-- Without coordinates the margin condition holds vacuously: no vector has norm `1`. -/
theorem zeroFeature_margin : ∀ v : Fin 0 → ℝ, ‖v‖ = 1 →
    (1 : ℝ) ≤ (P.map (O 0)).real {z | (1 : ℝ) ≤ v ⬝ᵥ (zeroFeature z.1 - 0)} := by
  intro v hv
  rw [Subsingleton.elim v 0, norm_zero] at hv
  norm_num at hv

omit [IsProbabilityMeasure P] in
/-- Every record of the one arm record law is in the treated arm. -/
theorem zeroFeature_prob_arm (hlaw : P.map (O 0) = oneArmRecordLaw) :
    0 < (P.map (O 0)).real {z : Bool × Bool × ℝ | z.2.1 = true} := by
  have hS : MeasurableSet {z : Bool × Bool × ℝ | z.2.1 = true} :=
    measurableSet_eq_fun measurable_snd.fst measurable_const
  rw [hlaw, oneArmRecordLaw, map_measureReal_apply measurable_oneArmRecord hS]
  have : oneArmRecord ⁻¹' {z : Bool × Bool × ℝ | z.2.1 = true} = Set.univ := by
    ext z; simp [oneArmRecord]
  rw [this, probReal_univ]
  exact one_pos

/-- **Bootstrap coverage without matching.** For an i.i.d. sample of the one arm record law,
`α ∈ (0, 1)` and `Φ(z) = 1 - α/2`, the bootstrap percentile and basic intervals of the weighted
arm mean cover `1/2` with probability tending to `1 - α`. -/
theorem zeroFeature_bootstrap_coverage (hO : IsIIDSample O P)
    (hlaw : P.map (O 0) = oneArmRecordLaw) {α z : ℝ} (hα : α ∈ Ioo (0 : ℝ) 1)
    (hz : cdf (gaussianReal 0 1) z = 1 - α / 2) :
    Tendsto (fun n => P.real {ω | (1 / 2 : ℝ) ∈
        percentileInterval (bootstrapLaw (bootstrapArmMean zeroFeature 0 true) O n ω) α})
        atTop (𝓝 (1 - α)) ∧
      Tendsto (fun n => P.real {ω | (1 / 2 : ℝ) ∈
        basicInterval (bootstrapLaw (bootstrapArmMean zeroFeature 0 true) O n ω)
          (sampleBalancedArmMean zeroFeature 0 O true n ω) α}) atTop (𝓝 (1 - α)) := by
  have hmargin := zeroFeature_margin (P := P) (O := O)
  have hq := zeroFeature_prob_arm (P := P) hlaw
  have h := tendsto_bootstrapArmMean_coverage hO measurable_zeroFeature (B := 0)
    (fun x => by simp [zeroFeature]) one_pos hmargin true hq
    (by rw [hlaw]; exact oneArm_memLp_outcome)
    (by rw [hlaw, zeroFeature_weightedArmVariance]; norm_num) hα hz
  rwa [hlaw, zeroFeature_tiltArmMean] at h

/-- **Bootstrap coverage of the unanchored comparison without matching.** For an i.i.d. sample
of the one arm record law and a reported aggregate mean `c`, the bootstrap percentile and basic
intervals of `c - m*_true` cover `c - 1/2` with probability tending to `1 - α`. -/
theorem zeroFeature_unanchored_bootstrap_coverage (hO : IsIIDSample O P)
    (hlaw : P.map (O 0) = oneArmRecordLaw) (c : ℝ) {α z : ℝ} (hα : α ∈ Ioo (0 : ℝ) 1)
    (hz : cdf (gaussianReal 0 1) z = 1 - α / 2) :
    Tendsto (fun n => P.real {ω | c - 1 / 2 ∈
        percentileInterval (bootstrapLaw (fun n y => c - bootstrapArmMean zeroFeature 0 true n y)
          O n ω) α}) atTop (𝓝 (1 - α)) ∧
      Tendsto (fun n => P.real {ω | c - 1 / 2 ∈
        basicInterval (bootstrapLaw (fun n y => c - bootstrapArmMean zeroFeature 0 true n y)
          O n ω) (c - sampleBalancedArmMean zeroFeature 0 O true n ω) α}) atTop
        (𝓝 (1 - α)) := by
  have h := tendsto_bootstrapUnanchored_coverage hO measurable_zeroFeature (B := 0)
    (fun x => by simp [zeroFeature]) one_pos zeroFeature_margin (zeroFeature_prob_arm hlaw)
    (by rw [hlaw]; exact oneArm_memLp_outcome) c
    (by rw [hlaw, zeroFeature_weightedArmVariance]; norm_num) hα hz
  rwa [hlaw, zeroFeature_tiltArmMean] at h

/-- **The instance is not vacuous**: there is a probability space carrying an i.i.d. sample of
the one arm record law, and on it the bootstrap percentile interval of the weighted arm mean
covers `1/2` with probability tending to `1 - α`. -/
theorem exists_zeroFeature_bootstrap_coverage {α z : ℝ} (hα : α ∈ Ioo (0 : ℝ) 1)
    (hz : cdf (gaussianReal 0 1) z = 1 - α / 2) :
    ∃ Ω : Type, ∃ _ : MeasurableSpace Ω, ∃ P : Measure Ω, ∃ O : ℕ → Ω → Bool × Bool × ℝ,
      IsProbabilityMeasure P ∧ IsIIDSample O P ∧ P.map (O 0) = oneArmRecordLaw ∧
        Tendsto (fun n => P.real {ω | (1 / 2 : ℝ) ∈
          percentileInterval (bootstrapLaw (bootstrapArmMean zeroFeature 0 true) O n ω) α})
          atTop (𝓝 (1 - α)) := by
  obtain ⟨Ω, mΩ, P, O, hP, -, hO, hlaw⟩ := exists_isIIDSample oneArmRecordLaw
  exact ⟨Ω, mΩ, P, O, hP, hO, (hlaw 0).map_eq,
    (zeroFeature_bootstrap_coverage hO (hlaw 0).map_eq hα hz).1⟩

end PopulationAdjustment

end CausalInference
