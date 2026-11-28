/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.PopulationAdjustment.WeightedNormalityVarianceDegenerate
public import CausalInference.PopulationAdjustment.WeightedNormalityVarianceCompare

/-!
# When the asymptotic variance of the weighted arm mean vanishes

Write `w₀ = w_{β₀}` for the population tilt, `m₀` for the weighted arm mean, `M` for the tilted
second moment `E[w₀ (φ(X) - t)(φ(X) - t)ᵀ]` and `c` for the coupling vector. The influence
function is `IF = (U - ℓ) / q` with the weighted residual `U = 1{A = a} w₀ (Y - m₀)` and the
projection term `ℓ = cᵀ M⁻¹ w₀ (φ(X) - t)` on the balance coordinates `w₀ (φ(X) - t)`.

* `weightedArmVariance_eq_zero_iff_residual`: `σ² = 0` if and only if `U = ℓ` almost surely.
* `weightedArmVariance_eq_zero_iff_exists_affine` (**the strong form in the model
  primitives**): `σ² = 0` if and only if for some `γ`,
  `1{A = a} (Y - m₀) = γᵀ (φ(X) - t)` almost surely. The tilt cancels because `w₀ > 0`; the
  coefficient is then `γ = M⁻¹ c`. So `σ² = 0` says: on the arm, `Y` is almost surely the
  affine function `m₀ + γᵀ(φ(X) - t)` of the matched features, and off the arm `γᵀ(φ(X) - t)`
  vanishes almost surely.
* `weightedArmVariance_eq_zero_iff_of_indepFun` (**randomization forces a constant outcome**):
  if `X ⫫ A` and `P(A ≠ a) > 0`, the margin condition rules out `γ ≠ 0` off the arm, and
  `σ² = 0` if and only if `Y = m₀` almost surely on the arm.
* `weightedArmVariance_eq_zero_of_ae_arm`: if every record is in arm `a` and `Y` is almost
  surely affine in the matched features, `Y = c₀ + γᵀ(φ(X) - t)`, then `m₀ = c₀` and `σ² = 0`.
* `oneArm_weightedArmVariance`, `oneArm_outcome_not_const`: an instance with a fair coin
  covariate, every record in the treated arm and the outcome `Y = 1{X}`, which is not almost
  surely constant; the asymptotic variance vanishes. The hypothesis `P(A ≠ a) > 0` of the
  randomized statement cannot be dropped.

## Main results

* `weightedArmProjection_eq_mul`, `weightedArmVariance_eq_zero_iff_residual`,
  `weightedArmVariance_eq_zero_iff_exists_affine`, `weightedArmVariance_eq_zero_iff_of_indepFun`,
  `weightedArmVariance_eq_zero_of_ae_arm`, `oneArm_weightedArmVariance`,
  `oneArm_outcome_not_const`.

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

open PointTreatment

variable {𝒳 : Type*} {p : ℕ} [MeasurableSpace 𝒳] {ν : Measure (𝒳 × Bool × ℝ)}

/-- The projection term is the tilt times a linear function of the centered features:
`ℓ = w₀ (cᵀ M⁻¹)(φ(X) - t)`. -/
theorem weightedArmProjection_eq_mul (ν : Measure (𝒳 × Bool × ℝ)) (φ : 𝒳 → Fin p → ℝ)
    (t : Fin p → ℝ) (a : Bool) (z : 𝒳 × Bool × ℝ) :
    weightedArmProjection ν φ t a z = tiltWeight φ t 0 (tiltMinimizer ν φ t) z.1 *
      ((weightedCoupling ν φ t a ᵥ* (tiltedSecondMoment ν φ t (tiltMinimizer ν φ t))⁻¹) ⬝ᵥ
        (φ z.1 - t)) := by
  rw [weightedArmProjection, dotProduct_mulVec]
  have : (fun j => tiltWeight φ t 0 (tiltMinimizer ν φ t) z.1 * (φ z.1 j - t j)) =
      tiltWeight φ t 0 (tiltMinimizer ν φ t) z.1 • (φ z.1 - t) := by
    funext j; simp [Pi.smul_apply, smul_eq_mul]
  rw [this, dotProduct_smul, smul_eq_mul]

/-- The weighted residual is the tilt times `1{A = a} (Y - m₀)`. -/
theorem weightedArmResidual_eq_mul (ν : Measure (𝒳 × Bool × ℝ)) (φ : 𝒳 → Fin p → ℝ)
    (t : Fin p → ℝ) (a : Bool) (z : 𝒳 × Bool × ℝ) :
    weightedArmResidual ν φ t a z = tiltWeight φ t 0 (tiltMinimizer ν φ t) z.1 *
      (armIndObs a z * (z.2.2 - tiltArmMean ν φ t a (tiltMinimizer ν φ t))) := by
  rw [weightedArmResidual]; ring

/-- **The asymptotic variance vanishes exactly when the weighted residual equals its
projection term almost surely**: `σ² = 0 ↔ U = ℓ` almost surely. -/
theorem weightedArmVariance_eq_zero_iff_residual [IsFiniteMeasure ν] {φ : 𝒳 → Fin p → ℝ}
    (hφ : Measurable φ) {t : Fin p → ℝ} {B : ℝ} (hB : ∀ x, ‖φ x - t‖ ≤ B) {δ : ℝ} (hδ : 0 < δ)
    (hmargin : ∀ v : Fin p → ℝ, ‖v‖ = 1 → δ ≤ ν.real {z | δ ≤ v ⬝ᵥ (φ z.1 - t)}) {a : Bool}
    (hq : 0 < ν.real {z | z.2.1 = a}) (hy : MemLp (fun z : 𝒳 × Bool × ℝ => z.2.2) 2 ν) :
    weightedArmVariance ν φ t a = 0 ↔
      weightedArmResidual ν φ t a =ᵐ[ν] weightedArmProjection ν φ t a := by
  have hmass : weightedArmMass ν φ t a ≠ 0 :=
    (integral_armIndObs_mul_tiltWeight_pos hφ hB (tiltMinimizer ν φ t) hq).ne'
  rw [weightedArmVariance_eq_zero_iff hφ hB hδ hmargin hq hy]
  constructor <;> intro h <;> filter_upwards [h] with z hz
  · rw [Pi.zero_apply, weightedArmInfluence_eq_residual_sub_projection, div_eq_zero_iff] at hz
    rcases hz with hz | hz
    · exact sub_eq_zero.1 hz
    · exact absurd hz hmass
  · rw [Pi.zero_apply, weightedArmInfluence_eq_residual_sub_projection, hz, sub_self, zero_div]

/-- **The coupling vector of an affine residual**: if `1{A = a} (Y - m₀) = γᵀ(φ(X) - t)` almost
surely, then `c = γᵀ M`. -/
theorem weightedCoupling_eq_vecMul [IsFiniteMeasure ν] {φ : 𝒳 → Fin p → ℝ}
    (hφ : Measurable φ) {t : Fin p → ℝ} {B : ℝ} (hB : ∀ x, ‖φ x - t‖ ≤ B) {a : Bool}
    {γ : Fin p → ℝ} (h : ∀ᵐ z ∂ν, armIndObs a z * (z.2.2 - tiltArmMean ν φ t a
      (tiltMinimizer ν φ t)) = γ ⬝ᵥ (φ z.1 - t)) :
    weightedCoupling ν φ t a = γ ᵥ* tiltedSecondMoment ν φ t (tiltMinimizer ν φ t) := by
  funext k
  set β₀ := tiltMinimizer ν φ t
  have hae : (fun z : 𝒳 × Bool × ℝ => armIndObs a z * tiltWeight φ t 0 β₀ z.1 *
      (z.2.2 - tiltArmMean ν φ t a β₀) * (φ z.1 k - t k)) =ᵐ[ν]
      fun z => ∑ j, γ j * (tiltWeight φ t 0 β₀ z.1 * (φ z.1 j - t j) * (φ z.1 k - t k)) := by
    filter_upwards [h] with z hz
    have e : armIndObs a z * tiltWeight φ t 0 β₀ z.1 * (z.2.2 - tiltArmMean ν φ t a β₀) *
        (φ z.1 k - t k) = tiltWeight φ t 0 β₀ z.1 * (armIndObs a z *
          (z.2.2 - tiltArmMean ν φ t a β₀)) * (φ z.1 k - t k) := by ring
    rw [e, hz, dotProduct, Finset.mul_sum, Finset.sum_mul]
    exact Finset.sum_congr rfl fun j _ => by simp only [Pi.sub_apply]; ring
  simp only [weightedCoupling]
  rw [integral_congr_ae hae, integral_finsetSum _ fun j _ =>
    (integrable_tiltWeight_mul_feature hφ hB β₀ j k).const_mul (γ j)]
  simp only [vecMul, dotProduct, tiltedSecondMoment, of_apply]
  exact Finset.sum_congr rfl fun j _ => integral_const_mul _ _

/-- **The strong form**: under bounded features, the margin condition, `P(A = a) > 0` and
`E[Y²] < ∞`, the asymptotic variance of the weighted arm mean vanishes if and only if for some
`γ`, `1{A = a} (Y - m₀) = γᵀ(φ(X) - t)` almost surely, with `m₀` the weighted arm mean. -/
theorem weightedArmVariance_eq_zero_iff_exists_affine [IsFiniteMeasure ν] {φ : 𝒳 → Fin p → ℝ}
    (hφ : Measurable φ) {t : Fin p → ℝ} {B : ℝ} (hB : ∀ x, ‖φ x - t‖ ≤ B) {δ : ℝ} (hδ : 0 < δ)
    (hmargin : ∀ v : Fin p → ℝ, ‖v‖ = 1 → δ ≤ ν.real {z | δ ≤ v ⬝ᵥ (φ z.1 - t)}) {a : Bool}
    (hq : 0 < ν.real {z | z.2.1 = a}) (hy : MemLp (fun z : 𝒳 × Bool × ℝ => z.2.2) 2 ν) :
    weightedArmVariance ν φ t a = 0 ↔ ∃ γ : Fin p → ℝ, ∀ᵐ z ∂ν,
      armIndObs a z * (z.2.2 - tiltArmMean ν φ t a (tiltMinimizer ν φ t)) =
        γ ⬝ᵥ (φ z.1 - t) := by
  set β₀ := tiltMinimizer ν φ t
  set M := tiltedSecondMoment ν φ t β₀
  rw [weightedArmVariance_eq_zero_iff_residual hφ hB hδ hmargin hq hy]
  constructor
  · intro h
    refine ⟨weightedCoupling ν φ t a ᵥ* M⁻¹, ?_⟩
    filter_upwards [h] with z hz
    rw [weightedArmResidual_eq_mul, weightedArmProjection_eq_mul] at hz
    exact mul_left_cancel₀ (tiltWeight_pos _ _ _ _ _).ne' hz
  · rintro ⟨γ, hγ⟩
    have hc := weightedCoupling_eq_vecMul hφ hB hγ
    have hMu : IsUnit M.det :=
      isUnit_iff_ne_zero.2 (det_tiltedSecondMoment_ne_zero hφ hB hδ hmargin β₀)
    have hγ' : weightedCoupling ν φ t a ᵥ* M⁻¹ = γ := by
      rw [hc, vecMul_vecMul, mul_nonsing_inv _ hMu, vecMul_one]
    filter_upwards [hγ] with z hz
    rw [weightedArmResidual_eq_mul, weightedArmProjection_eq_mul, hγ', hz]

/-- **Randomization forces a constant outcome**: if in addition `X ⫫ A` and `P(A ≠ a) > 0`,
then `σ² = 0` if and only if `Y = m₀` almost surely on the arm `A = a`. Proof: off the arm the
strong form gives `γᵀ(φ(X) - t) = 0` almost surely; by independence the margin set
`{δ ≤ vᵀ(φ(X) - t)}` of `v = γ / ‖γ‖` meets `{A ≠ a}` with positive probability, so `γ = 0`. -/
theorem weightedArmVariance_eq_zero_iff_of_indepFun [IsFiniteMeasure ν] {φ : 𝒳 → Fin p → ℝ}
    (hφ : Measurable φ) {t : Fin p → ℝ} {B : ℝ} (hB : ∀ x, ‖φ x - t‖ ≤ B) {δ : ℝ} (hδ : 0 < δ)
    (hmargin : ∀ v : Fin p → ℝ, ‖v‖ = 1 → δ ≤ ν.real {z | δ ≤ v ⬝ᵥ (φ z.1 - t)}) {a : Bool}
    (hq : 0 < ν.real {z | z.2.1 = a}) (hy : MemLp (fun z : 𝒳 × Bool × ℝ => z.2.2) 2 ν)
    (hind : IndepFun (fun z : 𝒳 × Bool × ℝ => z.1) (fun z => z.2.1) ν)
    (hq' : 0 < ν.real {z | z.2.1 ≠ a}) :
    weightedArmVariance ν φ t a = 0 ↔
      ∀ᵐ z ∂ν, z.2.1 = a → z.2.2 = tiltArmMean ν φ t a (tiltMinimizer ν φ t) := by
  set m₀ := tiltArmMean ν φ t a (tiltMinimizer ν φ t)
  rw [weightedArmVariance_eq_zero_iff_exists_affine hφ hB hδ hmargin hq hy]
  constructor
  · rintro ⟨γ, hγ⟩
    have hγ0 : γ = 0 := by
      by_contra hne
      have hn : 0 < ‖γ‖ := norm_pos_iff.2 hne
      set v := ‖γ‖⁻¹ • γ
      have hv : ‖v‖ = 1 := by
        rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hn.ne']
      set S' : Set 𝒳 := {x | δ ≤ v ⬝ᵥ (φ x - t)}
      set T' : Set Bool := {b | b ≠ a}
      have hS' : MeasurableSet S' := by
        refine measurableSet_le measurable_const ?_
        simp only [dotProduct, Pi.sub_apply]
        exact Finset.measurable_sum _ fun j _ =>
          measurable_const.mul (((measurable_pi_apply j).comp hφ).sub_const _)
      have hT' : MeasurableSet T' := MeasurableSet.of_discrete
      have hmul := hind.measure_inter_preimage_eq_mul S' T' hS' hT'
      have hpos : 0 < ν ((fun z : 𝒳 × Bool × ℝ => z.1) ⁻¹' S' ∩
          (fun z : 𝒳 × Bool × ℝ => z.2.1) ⁻¹' T') := by
        rw [hmul]
        have h1 : 0 < ν ((fun z : 𝒳 × Bool × ℝ => z.1) ⁻¹' S') := by
          have := lt_of_lt_of_le hδ (hmargin v hv)
          exact (ENNReal.toReal_pos_iff.1 this).1
        have h2 : 0 < ν ((fun z : 𝒳 × Bool × ℝ => z.2.1) ⁻¹' T') :=
          (ENNReal.toReal_pos_iff.1 hq').1
        exact ENNReal.mul_pos h1.ne' h2.ne'
      have hnull : ν {z | ¬ (armIndObs a z * (z.2.2 - m₀) = γ ⬝ᵥ (φ z.1 - t))} = 0 :=
        ae_iff.1 hγ
      refine absurd (measure_mono_null (fun z hz => ?_) hnull) hpos.ne'
      obtain ⟨hzS, hzT⟩ := hz
      simp only [Set.mem_preimage, S', T', Set.mem_ofPred_eq] at hzS hzT
      simp only [Set.mem_ofPred_eq, armIndObs, hzT, ite_false, zero_mul]
      intro h0
      have hγv : γ = ‖γ‖ • v := by
        simp only [v, smul_smul, mul_inv_cancel₀ hn.ne', one_smul]
      rw [hγv, smul_dotProduct, smul_eq_mul] at h0
      nlinarith
    filter_upwards [hγ] with z hz hza
    simp only [hγ0, zero_dotProduct, armIndObs, hza, ite_true, one_mul] at hz
    exact sub_eq_zero.1 hz
  · intro h
    refine ⟨0, ?_⟩
    filter_upwards [h] with z hz
    rw [zero_dotProduct, armIndObs]
    split_ifs with hza
    · rw [hz hza, sub_self, mul_zero]
    · rw [zero_mul]

/-- **One arm with an affine outcome**: if every record is in arm `a` and
`Y = c₀ + γᵀ(φ(X) - t)` almost surely, then the weighted arm mean is `c₀` and the asymptotic
variance vanishes, for any `γ`. -/
theorem weightedArmVariance_eq_zero_of_ae_arm [IsProbabilityMeasure ν] {φ : 𝒳 → Fin p → ℝ}
    (hφ : Measurable φ) {t : Fin p → ℝ} {B : ℝ} (hB : ∀ x, ‖φ x - t‖ ≤ B) {δ : ℝ} (hδ : 0 < δ)
    (hmargin : ∀ v : Fin p → ℝ, ‖v‖ = 1 → δ ≤ ν.real {z | δ ≤ v ⬝ᵥ (φ z.1 - t)}) {a : Bool}
    (hy : MemLp (fun z : 𝒳 × Bool × ℝ => z.2.2) 2 ν) (harm : ∀ᵐ z ∂ν, z.2.1 = a) {c₀ : ℝ}
    {γ : Fin p → ℝ} (hY : ∀ᵐ z ∂ν, z.2.2 = c₀ + γ ⬝ᵥ (φ z.1 - t)) :
    tiltArmMean ν φ t a (tiltMinimizer ν φ t) = c₀ ∧ weightedArmVariance ν φ t a = 0 := by
  set β₀ := tiltMinimizer ν φ t
  set w : 𝒳 × Bool × ℝ → ℝ := fun z => tiltWeight φ t 0 β₀ z.1
  have hq : 0 < ν.real {z | z.2.1 = a} := by
    have h1 : ν {z | z.2.1 = a}ᶜ = 0 := by
      rw [← ae_iff.1 harm]; rfl
    rw [measureReal_def, (prob_compl_eq_zero_iff (measurableSet_eq_fun measurable_snd.fst
      measurable_const)).1 h1]
    norm_num
  have hw1 : Integrable w ν := integrable_tiltWeight_fst hφ hB β₀
  have hden : ∫ z, armIndObs a z * w z ∂ν = ∫ z, w z ∂ν := by
    refine integral_congr_ae ?_
    filter_upwards [harm] with z hz
    simp [armIndObs, hz]
  have hnum : ∫ z, armIndObs a z * w z * z.2.2 ∂ν = c₀ * ∫ z, w z ∂ν := by
    have hae : (fun z => armIndObs a z * w z * z.2.2) =ᵐ[ν]
        fun z => c₀ * w z + ∑ j, γ j * (w z * (φ z.1 j - t j)) := by
      filter_upwards [harm, hY] with z hz hzY
      simp only [hzY, armIndObs, hz, ite_true, dotProduct, Finset.mul_sum, one_mul, mul_add]
      rw [mul_comm]
      congr 1
      exact Finset.sum_congr rfl fun j _ => by simp only [Pi.sub_apply]; ring
    have hfeat : ∀ j, Integrable (fun z : 𝒳 × Bool × ℝ => w z * (φ z.1 j - t j)) ν :=
      fun j => integrable_tiltWeight_mul hφ hB β₀
        (integrable_of_abs_le ((measurable_feature_fst hφ j).sub_const _) (C := B)
          fun z => abs_apply_le_of_norm_le (hB z.1) j)
    rw [integral_congr_ae hae, integral_add (hw1.const_mul c₀)
      (integrable_finsetSum _ fun j _ => (hfeat j).const_mul (γ j)),
      integral_finsetSum _ fun j _ => (hfeat j).const_mul (γ j), integral_const_mul]
    have h0 : ∀ j, ∫ z, γ j * (w z * (φ z.1 j - t j)) ∂ν = 0 := fun j => by
      rw [integral_const_mul, integral_tiltWeight_tiltMinimizer_mul_sub hφ hB hδ hmargin j,
        mul_zero]
    simp only [h0, Finset.sum_const_zero, add_zero]
  have hpos : 0 < ∫ z, w z ∂ν := by
    rw [← hden]; exact integral_armIndObs_mul_tiltWeight_pos hφ hB β₀ hq
  have hm : tiltArmMean ν φ t a β₀ = c₀ := by
    rw [tiltArmMean]
    change (∫ z, armIndObs a z * w z * z.2.2 ∂ν) / ∫ z, armIndObs a z * w z ∂ν = c₀
    rw [hnum, hden]
    field_simp
  refine ⟨hm, (weightedArmVariance_eq_zero_iff_exists_affine hφ hB hδ hmargin hq hy).2
    ⟨γ, ?_⟩⟩
  filter_upwards [harm, hY] with z hz hzY
  simp only [armIndObs, hz, ite_true, one_mul, hzY]
  rw [show tiltArmMean ν φ t a (tiltMinimizer ν φ t) = c₀ from hm]
  ring

/-! ### An instance with a nonconstant outcome -/

/-- The record `(X, true, 1{X})`: every unit in the treated arm, outcome `1{X}`. -/
def oneArmRecord (z : Bool × Bool × ℝ) : Bool × Bool × ℝ := (z.1, true, exampleInd z.1)

theorem measurable_oneArmRecord : Measurable oneArmRecord :=
  measurable_fst.prodMk (measurable_const.prodMk
    ((measurable_of_countable exampleInd).comp measurable_fst))

/-- The law of the records `(X, true, 1{X})` for a fair coin `X`. -/
noncomputable def oneArmRecordLaw : Measure (Bool × Bool × ℝ) :=
  exampleRecordLaw.map oneArmRecord

instance : IsProbabilityMeasure oneArmRecordLaw :=
  (Measure.isProbabilityMeasure_map_iff measurable_oneArmRecord.aemeasurable).2 inferInstance

theorem ae_oneArmRecordLaw_arm : ∀ᵐ z ∂oneArmRecordLaw, z.2.1 = true :=
  (ae_map_iff measurable_oneArmRecord.aemeasurable
    (measurableSet_eq_fun measurable_snd.fst measurable_const)).2 (ae_of_all _ fun _ => rfl)

/-- The outcome is `1{X} = 1/2 + (φ(X) - 1/2)`. -/
theorem ae_oneArmRecordLaw_outcome : ∀ᵐ z ∂oneArmRecordLaw,
    z.2.2 = 1 / 2 + (fun _ => 1) ⬝ᵥ (exampleFeature z.1 - exampleTarget) := by
  have hm : Measurable fun z : Bool × Bool × ℝ =>
      1 / 2 + (fun _ => (1 : ℝ)) ⬝ᵥ (exampleFeature z.1 - exampleTarget) :=
    (measurable_of_countable fun x : Bool =>
      1 / 2 + (fun _ => (1 : ℝ)) ⬝ᵥ (exampleFeature x - exampleTarget)).comp measurable_fst
  refine (ae_map_iff measurable_oneArmRecord.aemeasurable
    (measurableSet_eq_fun measurable_snd.snd hm)).2 (ae_of_all _ fun z => ?_)
  simp [oneArmRecord, dotProduct, exampleFeature, exampleTarget]

theorem oneArm_margin : ∀ v : Fin 1 → ℝ, ‖v‖ = 1 → (1 / 2 : ℝ) ≤
    oneArmRecordLaw.real {z | 1 / 2 ≤ v ⬝ᵥ (exampleFeature z.1 - exampleTarget)} := by
  intro v hv
  have hS : MeasurableSet {z : Bool × Bool × ℝ |
      1 / 2 ≤ v ⬝ᵥ (exampleFeature z.1 - exampleTarget)} :=
    measurableSet_le measurable_const
      ((measurable_of_countable fun x : Bool => v ⬝ᵥ (exampleFeature x - exampleTarget)).comp
        measurable_fst)
  rw [oneArmRecordLaw, map_measureReal_apply measurable_oneArmRecord hS]
  exact example_margin v hv

theorem oneArm_memLp_outcome :
    MemLp (fun z : Bool × Bool × ℝ => z.2.2) 2 oneArmRecordLaw := by
  refine MemLp.of_bound measurable_snd.snd.aestronglyMeasurable 1 ?_
  refine (ae_map_iff measurable_oneArmRecord.aemeasurable ?_).2 (ae_of_all _ fun z => ?_)
  · exact measurableSet_le (measurable_snd.snd.norm) measurable_const
  · simp only [oneArmRecord, exampleInd]
    split_ifs <;> norm_num

/-- **The asymptotic variance vanishes in the one arm model**, and the weighted arm mean is
`1/2`. -/
theorem oneArm_weightedArmVariance :
    tiltArmMean oneArmRecordLaw exampleFeature exampleTarget true
        (tiltMinimizer oneArmRecordLaw exampleFeature exampleTarget) = 1 / 2 ∧
      weightedArmVariance oneArmRecordLaw exampleFeature exampleTarget true = 0 :=
  weightedArmVariance_eq_zero_of_ae_arm (measurable_of_countable _) example_bound
    (by norm_num : (0 : ℝ) < 1 / 2) oneArm_margin oneArm_memLp_outcome ae_oneArmRecordLaw_arm
    ae_oneArmRecordLaw_outcome

/-- **The outcome of the one arm model is not almost surely constant**. -/
theorem oneArm_outcome_not_const (c : ℝ) : ¬ ∀ᵐ z ∂oneArmRecordLaw, z.2.2 = c := by
  intro h
  have h' := (ae_map_iff measurable_oneArmRecord.aemeasurable
    (measurableSet_eq_fun measurable_snd.snd measurable_const)).1 h
  have hnull : exampleRecordLaw {z | ¬ (oneArmRecord z).2.2 = c} = 0 := ae_iff.1 h'
  have hx : ∀ b : Bool, exampleRecordLaw.real {z | z.1 = b} = 1 / 2 := by
    intro b
    rw [exampleRecordLaw_real (measurableSet_eq_fun measurable_fst measurable_const)]
    cases b <;> simp [Set.indicator, exampleRecord] <;> norm_num
  have key : ∀ b : Bool, exampleInd b ≠ c → False := by
    intro b hb
    have h0 : exampleRecordLaw {z | z.1 = b} = 0 :=
      measure_mono_null (fun z hz => by
        simp only [Set.mem_ofPred_eq] at hz ⊢
        simpa [oneArmRecord, hz] using hb) hnull
    have := hx b
    rw [measureReal_def, h0, ENNReal.toReal_zero] at this
    norm_num at this
  by_cases hc : c = 1
  · exact key false (by simp [exampleInd, hc])
  · exact key true (by simpa [exampleInd, eq_comm] using hc)

end PopulationAdjustment

end CausalInference
