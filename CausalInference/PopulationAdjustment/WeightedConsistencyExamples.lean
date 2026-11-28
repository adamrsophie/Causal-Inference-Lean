/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.PopulationAdjustment.WeightedConsistencyContrast
public import CausalInference.IndirectComparison.CommonComparator

/-!
# A concrete model for the consistency of the weighted comparisons

A binary covariate `X` and a randomized binary arm `A` are independent fair coins. The matched
feature is `φ(x) = 1{x}` and the reported target mean is `t = 1/2`. The outcome is the arm
regression `Y = μ_A(X)` with `μ_true(x) = 1 + 2·1{x}` and `μ_false(x) = 1{x}`, affine in the
feature.

Every hypothesis of `sampleBalancedArmMean_isConsistent` is verified for this law of the records:
independence of `X` and `A`, `P(A = a) = 1/2`, the regression with residual variance `0`, bounded
features (`‖φ(x) - t‖ ≤ 1`) and the margin condition with `δ = 1/2` (both directions `v = ±1`
put mass `1/2` on `v(φ(X) - t) ≥ 1/2`). The weighted arm means are consistent for the computed
limits `2` and `1/2` (`exampleArmMean_isConsistent_true`, `exampleArmMean_isConsistent_false`).
For a target population with a fair coin covariate the three comparisons of
`WeightedConsistencyContrast` apply with all hypotheses verified (`example_unanchored`,
`example_anchored`, `example_anchored_identity`). An i.i.d. sample with this record law exists
(`exists_exampleSample`).

## Main definitions

* `exampleRegression`, `exampleFeature`, `exampleTarget`, `exampleRecordLaw`,
  `exampleTargetPopulation`.

## Main results

* `exampleArmMean_isConsistent_true`, `exampleArmMean_isConsistent_false`.
* `example_armMean_target`: the limit is the target arm mean.
* `example_trial`: the same model as the individual data of a randomized `Trial`.
* `example_unanchored`, `example_anchored`, `example_anchored_identity`.
* `exists_exampleArmMean_isConsistent`.

## References

* J. Hainmueller, *Entropy balancing for causal effects: a multivariate reweighting method to
  produce balanced samples in observational studies*, Political Analysis 20 (2012).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Finset
open scoped Topology

namespace CausalInference

namespace PopulationAdjustment

open PointTreatment IndirectComparison EffectMeasure

/-! ### The model -/

/-- The indicator `1{x}` of the binary covariate. -/
def exampleInd (x : Bool) : ℝ := if x then 1 else 0

/-- The arm regressions `μ_true(x) = 1 + 2·1{x}` and `μ_false(x) = 1{x}`. -/
def exampleRegression (a x : Bool) : ℝ := if a then 1 + 2 * exampleInd x else exampleInd x

/-- The matched feature `φ(x) = 1{x}`. -/
def exampleFeature (x : Bool) : Fin 1 → ℝ := fun _ => exampleInd x

/-- The reported target mean `t = 1/2`. -/
noncomputable def exampleTarget : Fin 1 → ℝ := fun _ => 1 / 2

/-- The record `(X, A, μ_A(X))` of the coins `(X, A)`. -/
def exampleRecord (q : Bool × Bool) : Bool × Bool × ℝ := (q.1, q.2, exampleRegression q.2 q.1)

/-- The law of the index trial records: two independent fair coins `X`, `A` and `Y = μ_A(X)`. -/
noncomputable def exampleRecordLaw : Measure (Bool × Bool × ℝ) := uniformPairLaw.map exampleRecord

theorem measurable_exampleRecord : Measurable exampleRecord := measurable_of_countable _

instance : IsProbabilityMeasure exampleRecordLaw := by
  unfold exampleRecordLaw; infer_instance

/-- The probability of a measurable set of records is the average over the four coin outcomes. -/
theorem exampleRecordLaw_real {S : Set (Bool × Bool × ℝ)} (hS : MeasurableSet S) :
    exampleRecordLaw.real S = (S.indicator 1 (exampleRecord (true, true)) +
      S.indicator 1 (exampleRecord (true, false)) + S.indicator 1 (exampleRecord (false, true)) +
      S.indicator 1 (exampleRecord (false, false))) / 4 := by
  rw [exampleRecordLaw, map_measureReal_apply measurable_exampleRecord hS,
    ← integral_indicator_one (measurable_exampleRecord hS), integral_uniformPairLaw]
  simp only [Set.indicator, Pi.one_apply]
  rfl

/-- Almost every record satisfies `Y = μ_A(X)`. -/
theorem ae_exampleRecordLaw_outcome :
    ∀ᵐ z ∂exampleRecordLaw, z.2.2 = exampleRegression z.2.1 z.1 := by
  have hm : Measurable fun z : Bool × Bool × ℝ => exampleRegression z.2.1 z.1 :=
    (measurable_from_prod_countable_left (f := fun q : Bool × Bool => exampleRegression q.2 q.1)
      fun _ => measurable_of_countable _).comp (measurable_fst.prodMk measurable_snd.fst)
  rw [exampleRecordLaw, ae_map_iff measurable_exampleRecord.aemeasurable
    (measurableSet_eq_fun measurable_snd.snd hm)]
  exact ae_of_all _ fun q => rfl

/-! ### The hypotheses on the record law -/

theorem example_indep :
    IndepFun (fun z : Bool × Bool × ℝ => z.1) (fun z => z.2.1) exampleRecordLaw := by
  have h1 : Measurable fun z : Bool × Bool × ℝ => z.1 := measurable_fst
  have h2 : Measurable fun z : Bool × Bool × ℝ => z.2.1 := measurable_snd.fst
  rw [indepFun_iff_map_prod_eq_prod_map_map h1.aemeasurable h2.aemeasurable, exampleRecordLaw,
    Measure.map_map (h1.prodMk h2) measurable_exampleRecord,
    Measure.map_map h1 measurable_exampleRecord, Measure.map_map h2 measurable_exampleRecord]
  have hid : ((fun z : Bool × Bool × ℝ => (z.1, z.2.1)) ∘ exampleRecord) = id := by
    funext q; rfl
  have hfst : ((fun z : Bool × Bool × ℝ => z.1) ∘ exampleRecord) = Prod.fst := by
    funext q; rfl
  have hsnd : ((fun z : Bool × Bool × ℝ => z.2.1) ∘ exampleRecord) = Prod.snd := by
    funext q; rfl
  rw [hid, hfst, hsnd, Measure.map_id, uniformPairLaw, Measure.map_fst_prod,
    Measure.map_snd_prod, measure_univ, one_smul]

theorem example_prob_arm (a : Bool) : exampleRecordLaw.real {z | z.2.1 = a} = 1 / 2 := by
  rw [exampleRecordLaw_real (measurableSet_eq_fun measurable_snd.fst measurable_const)]
  cases a <;> simp [Set.indicator, exampleRecord] <;> norm_num

theorem example_regression_measurable : ∀ s, Measurable (exampleRegression s) :=
  fun _ => measurable_of_countable _

theorem example_res2 : Integrable (fun z : Bool × Bool × ℝ =>
    (z.2.2 - exampleRegression z.2.1 z.1) ^ 2) exampleRecordLaw :=
  (integrable_zero _ _ _).congr (ae_exampleRecordLaw_outcome.mono fun z hz => by simp [hz])

theorem example_reg : exampleRecordLaw[fun z => z.2.2 | MeasurableSpace.comap
    (fun z : Bool × Bool × ℝ => (z.1, z.2.1)) inferInstance] =ᵐ[exampleRecordLaw]
      fun z => exampleRegression z.2.1 z.1 := by
  have hpair : Measurable fun z : Bool × Bool × ℝ => (z.1, z.2.1) :=
    measurable_fst.prodMk measurable_snd.fst
  have hsm : StronglyMeasurable[MeasurableSpace.comap (fun z : Bool × Bool × ℝ => (z.1, z.2.1))
      inferInstance] fun z => exampleRegression z.2.1 z.1 :=
    ((measurable_of_countable fun q : Bool × Bool => exampleRegression q.2 q.1).comp
      (comap_measurable _)).stronglyMeasurable
  have hint : Integrable (fun z : Bool × Bool × ℝ => exampleRegression z.2.1 z.1)
      exampleRecordLaw :=
    (integrable_const (3 : ℝ)).mono' (hsm.mono hpair.comap_le).aestronglyMeasurable
      (ae_of_all _ fun z => by
        rcases z with ⟨x, a, y⟩
        cases x <;> cases a <;> norm_num [exampleRegression, exampleInd])
  refine (condExp_congr_ae ae_exampleRecordLaw_outcome).trans ?_
  exact (condExp_of_stronglyMeasurable hpair.comap_le hsm hint).eventuallyEq

theorem example_var : exampleRecordLaw[fun z => (z.2.2 - exampleRegression z.2.1 z.1) ^ 2 |
    MeasurableSpace.comap (fun z : Bool × Bool × ℝ => (z.1, z.2.1)) inferInstance]
      ≤ᵐ[exampleRecordLaw] fun _ => (0 : ℝ) := by
  have h0 : (fun z : Bool × Bool × ℝ => (z.2.2 - exampleRegression z.2.1 z.1) ^ 2)
      =ᵐ[exampleRecordLaw] fun _ => (0 : ℝ) :=
    ae_exampleRecordLaw_outcome.mono fun z hz => by simp [hz]
  refine (condExp_congr_ae h0).le.trans ?_
  rw [condExp_const (measurable_fst.prodMk measurable_snd.fst).comap_le]

theorem example_bound (x : Bool) : ‖exampleFeature x - exampleTarget‖ ≤ 1 := by
  refine (pi_norm_le_iff_of_nonneg zero_le_one).2 fun _ => ?_
  cases x <;> simp [exampleFeature, exampleTarget, exampleInd] <;> norm_num

theorem example_margin : ∀ v : Fin 1 → ℝ, ‖v‖ = 1 → (1 / 2 : ℝ) ≤
    exampleRecordLaw.real {z | 1 / 2 ≤ v ⬝ᵥ (exampleFeature z.1 - exampleTarget)} := by
  intro v hv
  have hv0 : |v 0| = 1 := by
    rw [← Real.norm_eq_abs, ← hv]
    refine le_antisymm (norm_le_pi_norm v 0) ((pi_norm_le_iff_of_nonneg (norm_nonneg _)).2
      fun i => by rw [Subsingleton.elim i 0])
  have hS : MeasurableSet {z : Bool × Bool × ℝ |
      1 / 2 ≤ v ⬝ᵥ (exampleFeature z.1 - exampleTarget)} :=
    measurableSet_le measurable_const
      ((measurable_of_countable fun x : Bool => v ⬝ᵥ (exampleFeature x - exampleTarget)).comp
        measurable_fst)
  rw [exampleRecordLaw_real hS]
  rcases abs_eq (zero_le_one) |>.1 hv0 with h | h <;>
    simp [Set.indicator, exampleRecord, dotProduct, exampleFeature, exampleTarget, exampleInd,
      h] <;> norm_num

/-! ### Consistency of the weighted arm means -/

section Sample

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {O : ℕ → Ω → Bool × Bool × ℝ}

theorem example_isConsistent_arm (hO : IsIIDSample O P) (hOm : ∀ i, Measurable (O i))
    (hlaw : P.map (O 0) = exampleRecordLaw) (a : Bool) {a0 : ℝ} {b : Fin 1 → ℝ}
    (haff : ∀ x, exampleRegression a x = a0 + b ⬝ᵥ exampleFeature x) :
    IsConsistent (sampleBalancedArmMean exampleFeature exampleTarget O a)
      (a0 + b ⬝ᵥ exampleTarget) P :=
  sampleBalancedArmMean_isConsistent hO hOm (measurable_of_countable _) example_bound
    (by norm_num : (0 : ℝ) < 1 / 2) (by rw [hlaw]; exact example_margin)
    (by rw [hlaw]; exact example_indep) a (by rw [hlaw, example_prob_arm]; norm_num)
    example_regression_measurable (by rw [hlaw]; exact example_res2)
    (by rw [hlaw]; exact example_reg) (by rw [hlaw]; exact example_var) haff

/-- **The weighted arm mean of the index arm is consistent for `2`**: `μ_true = 1 + 2φ` and
`t = 1/2`. -/
theorem exampleArmMean_isConsistent_true (hO : IsIIDSample O P) (hOm : ∀ i, Measurable (O i))
    (hlaw : P.map (O 0) = exampleRecordLaw) :
    IsConsistent (sampleBalancedArmMean exampleFeature exampleTarget O true) 2 P := by
  have h := example_isConsistent_arm hO hOm hlaw true (a0 := 1) (b := fun _ => 2)
    fun x => by simp [exampleRegression, exampleFeature, dotProduct]
  convert h using 1
  norm_num [exampleTarget, dotProduct]

/-- **The weighted arm mean of the comparator arm is consistent for `1/2`**: `μ_false = φ`. -/
theorem exampleArmMean_isConsistent_false (hO : IsIIDSample O P) (hOm : ∀ i, Measurable (O i))
    (hlaw : P.map (O 0) = exampleRecordLaw) :
    IsConsistent (sampleBalancedArmMean exampleFeature exampleTarget O false) (1 / 2) P := by
  have h := example_isConsistent_arm hO hOm hlaw false (a0 := 0) (b := fun _ => 1)
    fun x => by simp [exampleRegression, exampleFeature, dotProduct]
  convert h using 1
  norm_num [exampleTarget, dotProduct]

end Sample

/-- An i.i.d. sample with the record law of the model exists. -/
theorem exists_exampleSample : ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω)
    (O : ℕ → Ω → Bool × Bool × ℝ), IsProbabilityMeasure P ∧ (∀ i, Measurable (O i)) ∧
      IsIIDSample O P ∧ P.map (O 0) = exampleRecordLaw := by
  obtain ⟨Ω, _, P, O, hP, hOm, hO, hlaw⟩ := exists_isIIDSample exampleRecordLaw
  exact ⟨Ω, _, P, O, hP, hOm, hO, (hlaw 0).map_eq⟩

/-- **The instance in closed form**: there is an i.i.d. sample of index trial records whose
weighted arm mean of the index arm, with entropy balancing weights at `t = 1/2`, is consistent
for `2`. -/
theorem exists_exampleArmMean_isConsistent : ∃ (Ω : Type) (_ : MeasurableSpace Ω)
    (P : Measure Ω) (_ : IsProbabilityMeasure P) (O : ℕ → Ω → Bool × Bool × ℝ),
      IsIIDSample O P ∧
        IsConsistent (sampleBalancedArmMean exampleFeature exampleTarget O true) 2 P := by
  obtain ⟨Ω, _, P, O, hP, hOm, hO, hlaw⟩ := exists_exampleSample
  exact ⟨Ω, _, P, hP, O, hO, exampleArmMean_isConsistent_true hO hOm hlaw⟩

/-! ### The comparisons -/

/-- The target population: a fair coin covariate, the index treatment `0` with outcome
`μ_true(X)`, the treatment `1` of the aggregate data trial with outcome `5`, and the comparator
`2` with outcome `μ_false(X)`. -/
noncomputable def exampleTargetPopulation : Population Bool Bool (Fin 3) :=
  ⟨halfLaw, id, ![exampleRegression true, fun _ => 5, exampleRegression false]⟩

theorem example_target_covLaw : exampleTargetPopulation.covLaw = halfLaw :=
  Measure.map_id

theorem example_target_mean (k : Fin 1) :
    ∫ x, exampleFeature x k ∂exampleTargetPopulation.covLaw = exampleTarget k := by
  rw [example_target_covLaw, integral_halfLaw]
  norm_num [exampleFeature, exampleTarget, exampleInd]

theorem example_target_armMean_zero : exampleTargetPopulation.armMean 0 = 2 := by
  change ∫ x, exampleRegression true x ∂halfLaw = 2
  rw [integral_halfLaw]; norm_num [exampleRegression, exampleInd]

theorem example_target_armMean_one : exampleTargetPopulation.armMean 1 = 5 := by
  change ∫ _x, (5 : ℝ) ∂halfLaw = 5
  rw [integral_halfLaw]; norm_num

theorem example_target_armMean_two : exampleTargetPopulation.armMean 2 = 1 / 2 := by
  change ∫ x, exampleRegression false x ∂halfLaw = 1 / 2
  rw [integral_halfLaw]; norm_num [exampleRegression, exampleInd]

instance : IsProbabilityMeasure exampleTargetPopulation.μ := by
  change IsProbabilityMeasure halfLaw; infer_instance

theorem example_target_isCondMean (a : Bool) (s : Fin 3)
    (hs : exampleTargetPopulation.Y s = exampleRegression a) :
    exampleTargetPopulation.IsCondMean s (exampleRegression a) :=
  Population.isCondMean_of_eq_comp measurable_id (measurable_of_countable _) hs
    (by rw [hs]; exact Integrable.of_finite)

theorem example_target_integrable (s : Fin 3) :
    Integrable (exampleTargetPopulation.Y s) exampleTargetPopulation.μ := Integrable.of_finite

section Sample

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {O : ℕ → Ω → Bool × Bool × ℝ}

/-- **The unanchored comparison in the model**: with the exact estimate `m̂_B = 5` of the target
mean of the aggregate data treatment, `m̂_B - μ̂_true → 5 - 2 = 3`. -/
theorem example_unanchored (hO : IsIIDSample O P) (hOm : ∀ i, Measurable (O i))
    (hlaw : P.map (O 0) = exampleRecordLaw) :
    IsConsistent (unanchoredBalancedEstimate id exampleFeature exampleTarget O fun _ _ => 5)
      3 P := by
  have h := unanchoredBalancedEstimate_isConsistent hO hOm (measurable_of_countable _)
    example_bound (by norm_num : (0 : ℝ) < 1 / 2) (by rw [hlaw]; exact example_margin)
    (by rw [hlaw]; exact example_indep) (by rw [hlaw, example_prob_arm]; norm_num)
    example_regression_measurable (by rw [hlaw]; exact example_res2)
    (by rw [hlaw]; exact example_reg) (by rw [hlaw]; exact example_var) (a0 := 1)
    (b := fun _ => 2) (fun x => by simp [exampleRegression, exampleFeature, dotProduct])
    (Q := exampleTargetPopulation) measurable_id example_target_mean (ta := 0) (tb := 1)
    (example_target_integrable 0) (example_target_isCondMean true 0 rfl)
    (by rw [example_target_armMean_one]; exact tendstoInMeasure_const 5) continuousAt_id
    continuousAt_id
  rw [Population.marginalEffect, example_target_armMean_zero, example_target_armMean_one] at h
  norm_num at h
  exact h

/-- **The anchored comparison on the log scale in the model**: with the exact estimate
`d̂_BC = log(1/2) - log 5` of the aggregate data trial,
`(log μ̂_false - log μ̂_true) - d̂_BC → log 5 - log 2`. -/
theorem example_anchored (hO : IsIIDSample O P) (hOm : ∀ i, Measurable (O i))
    (hlaw : P.map (O 0) = exampleRecordLaw) :
    IsConsistent (anchoredBalancedEstimate Real.log exampleFeature exampleTarget O
      fun _ _ => Real.log (1 / 2) - Real.log 5) (Real.log 5 - Real.log 2) P := by
  have h := anchoredBalancedEstimate_isConsistent hO hOm (measurable_of_countable _)
    example_bound (by norm_num : (0 : ℝ) < 1 / 2) (by rw [hlaw]; exact example_margin)
    (by rw [hlaw]; exact example_indep) (by rw [hlaw, example_prob_arm]; norm_num)
    (by rw [hlaw, example_prob_arm]; norm_num)
    (by rw [hlaw]; exact example_res2)
    (by rw [hlaw]; exact example_reg) (by rw [hlaw]; exact example_var) (a0A := 1)
    (bA := fun _ => 2) (a0C := 0) (bC := fun _ => 1)
    (fun x => by simp [exampleRegression, exampleFeature, dotProduct])
    (fun x => by simp [exampleRegression, exampleFeature, dotProduct])
    (Q := exampleTargetPopulation) measurable_id example_target_mean (ta := 0) (tb := 1)
    (tc := 2) (example_target_integrable 0) (example_target_integrable 2)
    (example_target_isCondMean true 0 rfl) (example_target_isCondMean false 2 rfl)
    (g := Real.log)
    (by rw [Population.marginalEffect, example_target_armMean_one, example_target_armMean_two]
        exact tendstoInMeasure_const _)
    (by rw [example_target_armMean_zero]; exact Real.continuousAt_log (by norm_num))
    (by rw [example_target_armMean_two]; exact Real.continuousAt_log (by norm_num))
  rwa [Population.marginalEffect, example_target_armMean_zero, example_target_armMean_one] at h

/-- **The anchored comparison on the identity scale in the model**: with the exact estimate
`d̂_BC = 1/2 - 5`, `(μ̂_false - μ̂_true) - d̂_BC → 5 - 2 = 3`. The hypothesis on the target is only
that `μ_false - μ_true` is the conditional mean of `Y(2) - Y(0)`. -/
theorem example_anchored_identity (hO : IsIIDSample O P) (hOm : ∀ i, Measurable (O i))
    (hlaw : P.map (O 0) = exampleRecordLaw) :
    IsConsistent (anchoredBalancedEstimate id exampleFeature exampleTarget O
      fun _ _ => 1 / 2 - 5) 3 P := by
  let R : Population Bool Bool Unit :=
    ⟨halfLaw, id, fun _ x => exampleRegression false x - exampleRegression true x⟩
  have hR : R.IsCondMean () fun x => exampleRegression false x - exampleRegression true x :=
    Population.isCondMean_of_eq_comp measurable_id (measurable_of_countable _) rfl
      Integrable.of_finite
  have h := anchoredBalancedEstimate_isConsistent_identity hO hOm (measurable_of_countable _)
    example_bound (by norm_num : (0 : ℝ) < 1 / 2) (by rw [hlaw]; exact example_margin)
    (by rw [hlaw]; exact example_indep) (by rw [hlaw, example_prob_arm]; norm_num)
    (by rw [hlaw, example_prob_arm]; norm_num)
    (by rw [hlaw]; exact example_res2)
    (by rw [hlaw]; exact example_reg) (by rw [hlaw]; exact example_var) (a0A := 1)
    (bA := fun _ => 2) (a0C := 0) (bC := fun _ => 1)
    (fun x => by simp [exampleRegression, exampleFeature, dotProduct])
    (fun x => by simp [exampleRegression, exampleFeature, dotProduct])
    (Q := exampleTargetPopulation) measurable_id example_target_mean (ta := 0) (tb := 1)
    (tc := 2) (example_target_integrable 0) (example_target_integrable 2) hR.2
    (by rw [Population.marginalEffect, example_target_armMean_one, example_target_armMean_two]
        exact tendstoInMeasure_const _)
  rw [Population.marginalEffect, example_target_armMean_zero, example_target_armMean_one,
    show (id 5 - id 2 : ℝ) = 3 by norm_num] at h
  exact h

/-- **The weighted arm mean is consistent for the target arm mean**: in the target population
the regression `μ_true` is the conditional mean of `Y(0)`, so the limit `2` is `E_Q[Y(0)]`. -/
theorem example_armMean_target (hO : IsIIDSample O P) (hOm : ∀ i, Measurable (O i))
    (hlaw : P.map (O 0) = exampleRecordLaw) :
    IsConsistent (sampleBalancedArmMean exampleFeature exampleTarget O true)
      (exampleTargetPopulation.armMean 0) P :=
  sampleBalancedArmMean_isConsistent_armMean hO hOm (measurable_of_countable _) example_bound
    (by norm_num : (0 : ℝ) < 1 / 2) (by rw [hlaw]; exact example_margin)
    (by rw [hlaw]; exact example_indep) true (by rw [hlaw, example_prob_arm]; norm_num)
    example_regression_measurable (by rw [hlaw]; exact example_res2)
    (by rw [hlaw]; exact example_reg) (by rw [hlaw]; exact example_var) (a0 := 1)
    (b := fun _ => 2) (fun x => by simp [exampleRegression, exampleFeature, dotProduct])
    measurable_id example_target_mean (example_target_integrable 0)
    (example_target_isCondMean true 0 rfl)

end Sample

/-! ### The index trial -/

/-- The index trial of the model: covariate and arm are the two coins, and the potential outcome
of arm `a` is `μ_a(X)`. Its individual data law is `exampleRecordLaw`. -/
noncomputable def exampleTrial : Trial (Bool × Bool) Bool Bool :=
  { μ := uniformPairLaw, X := Prod.fst, Y := fun a q => exampleRegression a q.1, A := Prod.snd }

theorem exampleTrial_ipdLaw : exampleTrial.ipdLaw = exampleRecordLaw := rfl

theorem exampleTrial_randomized : IndepFun exampleTrial.X exampleTrial.A exampleTrial.μ :=
  (indepFun_map_iff measurable_exampleRecord measurable_fst measurable_snd.fst).1 example_indep

theorem exampleTrial_prob_arm (a : Bool) :
    exampleTrial.μ.real (exampleTrial.A ⁻¹' {a}) = 1 / 2 := by
  have h := example_prob_arm a
  rwa [exampleRecordLaw, map_measureReal_apply measurable_exampleRecord
    (measurableSet_eq_fun measurable_snd.fst measurable_const)] at h

theorem exampleTrial_margin : ∀ v : Fin 1 → ℝ, ‖v‖ = 1 → (1 / 2 : ℝ) ≤
    exampleTrial.covLaw.real {x | 1 / 2 ≤ v ⬝ᵥ (exampleFeature x - exampleTarget)} := by
  intro v hv
  have hS : MeasurableSet {x : Bool | 1 / 2 ≤ v ⬝ᵥ (exampleFeature x - exampleTarget)} :=
    (Set.to_countable _).measurableSet
  have h := example_margin v hv
  rw [exampleRecordLaw, map_measureReal_apply measurable_exampleRecord
    (show MeasurableSet {z : Bool × Bool × ℝ |
      1 / 2 ≤ v ⬝ᵥ (exampleFeature z.1 - exampleTarget)} from measurable_fst hS)] at h
  rw [Population.covLaw, map_measureReal_apply (f := exampleTrial.X) measurable_fst hS]
  exact h

section Sample

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {O : ℕ → Ω → Bool × Bool × ℝ}

/-- **The trial form in the model**: an i.i.d. sample of the individual data of the randomized
index trial gives a weighted arm mean of the index arm consistent for `2`. -/
theorem example_trial (hO : IsIIDSample O P) (hOm : ∀ i, Measurable (O i))
    (hlaw : P.map (O 0) = exampleTrial.ipdLaw) :
    IsConsistent (sampleBalancedArmMean exampleFeature exampleTarget O true) 2 P := by
  have h := sampleBalancedArmMean_isConsistent_trial (T := exampleTrial) measurable_fst
    measurable_snd (measurable_of_countable _) exampleTrial_randomized hO hOm hlaw
    (measurable_of_countable _) example_bound (by norm_num : (0 : ℝ) < 1 / 2)
    exampleTrial_margin true (by rw [exampleTrial_prob_arm]; norm_num)
    example_regression_measurable example_res2 example_reg example_var (a0 := 1)
    (b := fun _ => 2) (fun x => by simp [exampleRegression, exampleFeature, dotProduct])
  convert h using 1
  norm_num [exampleTarget, dotProduct]

end Sample

/-- The entropy balancing weights of three units with the feature of the model are jointly
measurable in the reported moments and the covariates. -/
theorem example_measurable_weights :
    Measurable fun q : (Fin 1 → ℝ) × (Fin 3 → Bool) =>
      balancingWeights fun i => exampleFeature (q.2 i) - q.1 :=
  measurable_balancingWeights_features (measurable_of_countable _)

end PopulationAdjustment

end CausalInference
