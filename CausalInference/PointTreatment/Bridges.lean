/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.PointTreatment.Weighting
public import CausalInference.MissingData.Identification
public import CausalInference.PartialIdentification.IdentifiedSet

/-!
# Point treatment: bridges to missing data and to the Manski bounds

**Missing data.** Each arm of a point treatment problem is a missing data problem: the
covariate is `W`, the response indicator is `{A = a}` and the full outcome is `Y(a)`
(`PointTreatmentModel.armModel`). The observed data of the arm, `(W, 1{A = a}, 1{A = a} Y)`, is
a measurable function of the observed data `(W, A, Y)` of the point treatment problem, so the
law of the former is a pushforward of the law of the latter. Ignorability makes each arm missing
at random (`IndicatorIgnorable.marMean`, `Ignorable.mar`), the weighted outcomes agree, and the
identification of the full data mean under missing at random gives the **point identification
of the average effect** from the law of `(W, A, Y)`.

**Manski bounds.** A pair of potential outcomes is a `Manski.POModel` and conversely; the
observed outcome and the average effect agree. Every model with outcomes in `[lo, hi]` has its
average effect in the Manski interval. Under ignorability with a trivial covariate the average
effect equals the naive contrast of observed means, which therefore lies in the Manski interval.

## Main definitions

* `PointTreatmentModel`: a measure, a conditioning variable, a binary treatment and a pair of
  potential outcomes.
* `PointTreatmentModel.observedLaw`: the law of `(W, A, Y)`.
* `PointTreatmentModel.armModel M a`: the arm `a` as a `MissingData.MissingDataModel`.
* `PointTreatmentModel.IsIgnorablePositive`: probability measure, measurable variables,
  integrable potential outcomes, the indicator form of ignorability and positivity of both arms.
* `ateFunctional`: a functional of laws of `(W, A, Y)` that recovers the average effect.
* `toPOModel`, `ofPOModel`: the conversions with `Manski.POModel`.

## Main results

* `PointTreatmentModel.armModel_observedLaw`: the arm's observed law is a pushforward.
* `PointTreatmentModel.armModel_mem_marPositiveModels`: each arm is a positive model missing at
  random.
* `PointTreatmentModel.ipwTerm_eq_armModel`: the weighted outcomes agree.
* `PointTreatmentModel.ate_eq_ateFunctional`, `pointIdentified_ate`: the average effect is a
  function of the law of `(W, A, Y)` on `IsIgnorablePositive` models;
  `PointTreatmentModel.isIgnorablePositive_of_ignorable` gives the full form version and
  `PointTreatmentModel.pos_of_isPropensityScore` the positivity from a propensity score.
* `manski_ate_toPOModel`, `ate_mem_manskiBounds`, `ate_eq_naiveContrast_of_ignorable`,
  `naiveContrast_mem_manskiBounds_of_ignorable`.

## References

* C. F. Manski, *Nonparametric bounds on treatment effects*, American Economic Review 80 (1990).
* D. B. Rubin, *Inference and missing data*, Biometrika 63 (1976).
-/

@[expose] public section

namespace CausalInference

namespace PointTreatment

open MeasureTheory ProbabilityTheory MissingData Set

/-- A point treatment model: a measure, a conditioning variable `W`, a binary treatment `A` and
a pair of potential outcomes `Y`. -/
structure PointTreatmentModel (Ω 𝒲 : Type*) [MeasurableSpace Ω] where
  /-- The underlying measure. -/
  μ : Measure Ω
  /-- The conditioning variable (the covariates). -/
  W : Ω → 𝒲
  /-- The binary treatment. -/
  A : Ω → Bool
  /-- The potential outcomes. -/
  Y : Bool → Ω → ℝ

namespace PointTreatmentModel

variable {Ω 𝒲 : Type*} [MeasurableSpace Ω] [MeasurableSpace 𝒲]

/-- The observed data `(W, A, Y)`, with the observed outcome `Y = Y(A)`. -/
noncomputable def observedData (M : PointTreatmentModel Ω 𝒲) : Ω → 𝒲 × Bool × ℝ :=
  fun ω => (M.W ω, M.A ω, obsOutcome M.A M.Y ω)

/-- The law of the observed data `(W, A, Y)`. -/
noncomputable def observedLaw (M : PointTreatmentModel Ω 𝒲) : Measure (𝒲 × Bool × ℝ) :=
  M.μ.map M.observedData

/-- The arm `a` as a missing data model: covariate `W`, full outcome `Y(a)`, response
indicator `{A = a}`. -/
def armModel (M : PointTreatmentModel Ω 𝒲) (a : Bool) : MissingDataModel Ω 𝒲 :=
  ⟨M.μ, M.W, M.Y a, arm M.A a⟩

/-- The map from the observed data `(w, b, y)` of the point treatment problem to the observed
data `(w, 1{b = a}, 1{b = a} y)` of the arm `a`. -/
noncomputable def armProj (a : Bool) : 𝒲 × Bool × ℝ → 𝒲 × Bool × ℝ :=
  fun q => (q.1, q.2.1 == a, (if q.2.1 = a then 1 else 0) * q.2.2)

omit [MeasurableSpace Ω] in
theorem measurable_armProj (a : Bool) : Measurable (armProj (𝒲 := 𝒲) a) :=
  measurable_fst.prodMk
    (((Measurable.of_discrete (f := fun b : Bool => b == a)).comp measurable_snd.fst).prodMk
      (((Measurable.of_discrete (f := fun b : Bool => if b = a then (1 : ℝ) else 0)).comp
        measurable_snd.fst).mul measurable_snd.snd))

theorem measurable_observedData {M : PointTreatmentModel Ω 𝒲} (hW : Measurable M.W)
    (hA : Measurable M.A) (hY : ∀ a, Measurable (M.Y a)) : Measurable M.observedData :=
  hW.prodMk (hA.prodMk (measurable_obsOutcome hA hY))

omit [MeasurableSpace 𝒲] in
/-- The observed data of the arm `a` is a function of the observed data `(W, A, Y)`. -/
theorem armModel_observedData (M : PointTreatmentModel Ω 𝒲) (a : Bool) :
    (M.armModel a).observedData = armProj a ∘ M.observedData := by
  funext ω
  refine Prod.ext rfl (Prod.ext rfl ?_)
  change respInd (arm M.A a) ω * M.Y a ω = (if M.A ω = a then 1 else 0) * obsOutcome M.A M.Y ω
  rw [← respInd_arm_mul_obsOutcome, respInd_arm_apply]

/-- The observed law of the arm `a` is the pushforward of the law of `(W, A, Y)`. -/
theorem armModel_observedLaw {M : PointTreatmentModel Ω 𝒲} (hW : Measurable M.W)
    (hA : Measurable M.A) (hY : ∀ a, Measurable (M.Y a)) (a : Bool) :
    (M.armModel a).observedLaw = M.observedLaw.map (armProj a) := by
  rw [MissingDataModel.observedLaw, armModel_observedData, observedLaw,
    Measure.map_map (measurable_armProj a) (measurable_observedData hW hA hY)]
  rfl

omit [MeasurableSpace 𝒲] in
/-- The full data mean of the arm `a` is the arm mean `E[Y(a)]`. -/
theorem fullMean_armModel (M : PointTreatmentModel Ω 𝒲) (a : Bool) :
    (M.armModel a).fullMean = armMean M.μ M.Y a :=
  rfl

omit [MeasurableSpace 𝒲] in
/-- **The weighted outcomes agree**: the inverse probability weighted outcome of the arm `a` is
the weighted outcome `1{R} Y / π(X)` of the missing data model of the arm. -/
theorem ipwTerm_eq_armModel (M : PointTreatmentModel Ω 𝒲) (e : 𝒲 → ℝ) (a : Bool) :
    ipwTerm M.A M.Y M.W e a = fun ω =>
      respInd (M.armModel a).R ω * (M.armModel a).Y ω / armProb e a ((M.armModel a).X ω) := by
  funext ω
  simp only [ipwTerm, armModel]
  rw [respInd_arm_mul_obsOutcome]

/-- The assumptions under which the average effect is point identified: a probability measure,
measurable variables, integrable potential outcomes, the indicator form of ignorability and
positivity `P(A = a | W) > 0` of both arms. -/
structure IsIgnorablePositive (M : PointTreatmentModel Ω 𝒲) : Prop where
  /-- The underlying measure is a probability measure. -/
  isProbabilityMeasure : IsProbabilityMeasure M.μ
  /-- The conditioning variable is measurable. -/
  measurable_W : Measurable M.W
  /-- The treatment is measurable. -/
  measurable_A : Measurable M.A
  /-- The potential outcomes are measurable. -/
  measurable_Y : ∀ a, Measurable (M.Y a)
  /-- The potential outcomes are integrable. -/
  integrable_Y : ∀ a, Integrable (M.Y a) M.μ
  /-- Ignorability in indicator form. -/
  indicatorIgnorable : IndicatorIgnorable M.μ M.A M.W M.Y
  /-- Positivity of both arms: `P(A = a | W) > 0` almost surely. -/
  pos : ∀ a, ∀ᵐ ω ∂M.μ, 0 < M.μ[respInd (arm M.A a) | MeasurableSpace.comap M.W inferInstance] ω

/-- Positivity of both arms in `IsIgnorablePositive` follows from a propensity score `e` with
`0 < e(W) < 1` almost surely. -/
theorem pos_of_isPropensityScore {M : PointTreatmentModel Ω 𝒲} [IsFiniteMeasure M.μ]
    (hW : Measurable M.W) (hA : Measurable M.A) {e : 𝒲 → ℝ}
    (hps : IsPropensityScore M.μ M.A M.W e) (hov : OverlapAE e (M.μ.map M.W)) (a : Bool) :
    ∀ᵐ ω ∂M.μ, 0 < M.μ[respInd (arm M.A a) | MeasurableSpace.comap M.W inferInstance] ω := by
  filter_upwards [hps.condExp_arm hW hA a, armProb_pos_of_ae (hov.ae_comp hW.aemeasurable) a]
    with ω h1 h2
  rw [h1]
  exact h2

/-- **Each arm is a positive model missing at random** in the sense of
`MissingData.marPositiveModels`. -/
theorem armModel_mem_marPositiveModels {M : PointTreatmentModel Ω 𝒲}
    (hM : M.IsIgnorablePositive) (a : Bool) : M.armModel a ∈ marPositiveModels := by
  have := hM.isProbabilityMeasure
  exact ⟨⟨hM.isProbabilityMeasure, hM.measurable_W, measurable_arm hM.measurable_A a,
    hM.measurable_Y a⟩, hM.integrable_Y a,
    hM.indicatorIgnorable.marMean hM.measurable_W hM.measurable_A hM.measurable_Y a, hM.pos a⟩

/-- Under the full form of ignorability (`Ω` standard Borel) and positivity of both arms, a
model with measurable variables and integrable potential outcomes satisfies
`IsIgnorablePositive`. -/
theorem isIgnorablePositive_of_ignorable [StandardBorelSpace Ω] {M : PointTreatmentModel Ω 𝒲}
    [IsProbabilityMeasure M.μ] (hW : Measurable M.W) (hA : Measurable M.A)
    (hY : ∀ a, Measurable (M.Y a)) (hYi : ∀ a, Integrable (M.Y a) M.μ)
    (hign : Ignorable M.μ M.A hW M.Y)
    (hpos : ∀ a, ∀ᵐ ω ∂M.μ,
      0 < M.μ[respInd (arm M.A a) | MeasurableSpace.comap M.W inferInstance] ω) :
    M.IsIgnorablePositive :=
  ⟨inferInstance, hW, hA, hY, hYi, (ignorable_iff_indicatorIgnorable hW hA hY).1 hign, hpos⟩

end PointTreatmentModel

open PointTreatmentModel

variable {Ω 𝒲 : Type*} [MeasurableSpace Ω] [MeasurableSpace 𝒲]

/-- The functional of a law `ν` of `(W, A, Y)` that recovers the average effect: the difference
of the inverse probability weighting functionals of the pushforwards of `ν` to the observed data
of the two arms. -/
noncomputable def ateFunctional (ν : Measure (𝒲 × Bool × ℝ)) : ℝ :=
  ipwFunctional (ν.map (armProj true)) - ipwFunctional (ν.map (armProj false))

/-- **Identification of the average effect from the law of `(W, A, Y)`.** -/
theorem PointTreatmentModel.ate_eq_ateFunctional {M : PointTreatmentModel Ω 𝒲}
    (hM : M.IsIgnorablePositive) : ate M.μ M.Y = ateFunctional M.observedLaw := by
  rw [ate_eq_armMean_sub (hM.integrable_Y true) (hM.integrable_Y false), ateFunctional,
    ← armModel_observedLaw hM.measurable_W hM.measurable_A hM.measurable_Y,
    ← armModel_observedLaw hM.measurable_W hM.measurable_A hM.measurable_Y,
    ← fullMean_eq_ipwFunctional (armModel_mem_marPositiveModels hM true),
    ← fullMean_eq_ipwFunctional (armModel_mem_marPositiveModels hM false)]
  rfl

/-- **The average effect is point identified** from the law of the observed data `(W, A, Y)` on
the class of models satisfying `IsIgnorablePositive`. -/
theorem pointIdentified_ate :
    PointIdentified {M : PointTreatmentModel Ω 𝒲 | M.IsIgnorablePositive}
      PointTreatmentModel.observedLaw (fun M => ate M.μ M.Y) :=
  fun _ hM _ hM' h => by
    simp only
    rw [ate_eq_ateFunctional hM, ate_eq_ateFunctional hM', h]

/-! ### Manski bounds -/

/-- A pair of potential outcomes as a `Manski.POModel`. -/
def toPOModel (Y : Bool → Ω → ℝ) : Manski.POModel Ω := ⟨Y true, Y false⟩

/-- A `Manski.POModel` as a pair of potential outcomes. -/
def ofPOModel (m : Manski.POModel Ω) : Bool → Ω → ℝ := fun a => if a then m.Y1 else m.Y0

omit [MeasurableSpace Ω] in
@[simp] theorem ofPOModel_toPOModel (Y : Bool → Ω → ℝ) : ofPOModel (toPOModel Y) = Y := by
  funext a; cases a <;> rfl

omit [MeasurableSpace Ω] in
@[simp] theorem toPOModel_ofPOModel (m : Manski.POModel Ω) : toPOModel (ofPOModel m) = m := rfl

omit [MeasurableSpace Ω] in
/-- The observed outcomes agree. -/
theorem manski_observed_toPOModel (A : Ω → Bool) (Y : Bool → Ω → ℝ) :
    Manski.observed A (toPOModel Y) = obsOutcome A Y := by
  funext ω
  simp only [Manski.observed, toPOModel, obsOutcome]
  cases A ω <;> rfl

/-- The average effects agree when the potential outcomes are integrable (`Manski.ate` is a
difference of means, `ate` the mean of the difference). -/
theorem manski_ate_toPOModel {μ : Measure Ω} {Y : Bool → Ω → ℝ}
    (hYi : ∀ a, Integrable (Y a) μ) : Manski.ate μ (toPOModel Y) = ate μ Y :=
  (ate_eq_armMean_sub (hYi true) (hYi false)).symm

/-- A pair of measurable potential outcomes with values in `[lo, hi]` is a bounded Manski
model. -/
theorem toPOModel_mem_boundedModels {Y : Bool → Ω → ℝ} {lo hi : ℝ}
    (hY : ∀ a, Measurable (Y a)) (hb : ∀ a ω, Y a ω ∈ Icc lo hi) :
    toPOModel Y ∈ Manski.boundedModels lo hi :=
  ⟨hY true, hY false, hb true, hb false⟩

/-- **The average effect lies in the Manski interval** for measurable potential outcomes with
values in `[lo, hi]`, with no assumption on the treatment assignment. -/
theorem ate_mem_manskiBounds {μ : Measure Ω} [IsFiniteMeasure μ] {A : Ω → Bool}
    {Y : Bool → Ω → ℝ} {lo hi : ℝ} (hA : Measurable A) (hY : ∀ a, Measurable (Y a))
    (hb : ∀ a ω, Y a ω ∈ Icc lo hi) :
    ate μ Y ∈ Icc (Manski.boundY1 μ A lo (obsOutcome A Y) - Manski.boundY0 μ A hi (obsOutcome A Y))
      (Manski.boundY1 μ A hi (obsOutcome A Y) - Manski.boundY0 μ A lo (obsOutcome A Y)) := by
  have h := Manski.ate_mem_Icc (μ := μ) hA (toPOModel_mem_boundedModels hY hb)
  rwa [manski_observed_toPOModel, manski_ate_toPOModel
    (fun a => Manski.integrable_of_mem_Icc (hY a) (hb a))] at h

/-- On an arm of positive probability, the weighted mean of the observed outcome with the arm
probability as weight is the observed mean in that arm. -/
theorem integral_respInd_arm_mul_div {μ : Measure Ω} [IsFiniteMeasure μ] {A : Ω → Bool}
    (hA : Measurable A) (f : Ω → ℝ) (a : Bool) (h0 : μ.real (A ⁻¹' {a}) ≠ 0) :
    ∫ ω, respInd (arm A a) ω * f ω / μ.real (A ⁻¹' {a}) ∂μ = condMeanArm μ A a f := by
  have hind : (fun ω => respInd (arm A a) ω * f ω) = (A ⁻¹' {a}).indicator f := by
    funext ω
    classical
    rw [respInd_arm_apply, Set.indicator_apply]
    by_cases h : A ω = a <;> simp [h]
  rw [integral_div, hind, integral_indicator (hA (measurableSet_singleton a)),
    setIntegral_eq_measureReal_mul_condMeanArm, mul_div_cancel_left₀ _ h0]

/-- **Under ignorability with a trivial covariate the average effect is the naive contrast.**
If `A ⫫ (Y(0), Y(1))` (ignorability given a constant covariate) and `0 < P(A = 1) < 1`, then
`E[Y(1) - Y(0)] = E[Y | A = 1] - E[Y | A = 0]`. -/
theorem ate_eq_naiveContrast_of_ignorable [StandardBorelSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {A : Ω → Bool} {Y : Bool → Ω → ℝ} (hA : Measurable A)
    (hY : ∀ a, Measurable (Y a)) (hYi : ∀ a, Integrable (Y a) μ)
    (hign : Ignorable μ A (measurable_const (a := ())) Y)
    (h0 : 0 < μ.real (A ⁻¹' {true})) (h1 : μ.real (A ⁻¹' {true}) < 1) :
    ate μ Y = naiveContrast μ A Y := by
  have hW : Measurable fun _ : Ω => () := measurable_const
  set p := μ.real (A ⁻¹' {true}) with hp
  have hps : IsPropensityScore μ A (fun _ : Ω => ()) (fun _ => p) := by
    refine ⟨measurable_const, ?_⟩
    rw [MeasurableSpace.comap_const, condExp_bot]
    refine Filter.Eventually.of_forall fun _ => ?_
    simp only [respInd]
    rw [integral_indicator_one (hA (measurableSet_singleton true))]
  have hov : OverlapAE (fun _ : Unit => p) (μ.map fun _ : Ω => ()) :=
    Overlap.overlapAE (fun _ => ⟨h0, h1⟩) _
  rw [hign.ate_eq_ipw hW hA hY hYi hps hov]
  have hii := (ignorable_iff_indicatorIgnorable hW hA hY).1 hign
  have hpos := armProb_pos_of_ae (hov.ae_comp hW.aemeasurable)
  rw [integral_sub (hii.integrable_ipw hW hA hY hps true (hpos true) (hYi true))
    (hii.integrable_ipw hW hA hY hps false (hpos false) (hYi false))]
  have hfalse : armProb (fun _ : Unit => p) false () = μ.real (A ⁻¹' {false}) := by
    rw [armProb_false, measureReal_false_eq_one_sub hA]
  simp only [armProb_true]
  rw [hfalse, integral_respInd_arm_mul_div hA _ true h0.ne',
    integral_respInd_arm_mul_div hA _ false (by rw [measureReal_false_eq_one_sub hA]; linarith)]
  rfl

/-- **Under ignorability with a trivial covariate the naive contrast lies in the Manski
interval**, for measurable potential outcomes with values in `[lo, hi]`. -/
theorem naiveContrast_mem_manskiBounds_of_ignorable [StandardBorelSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {A : Ω → Bool} {Y : Bool → Ω → ℝ} {lo hi : ℝ} (hA : Measurable A)
    (hY : ∀ a, Measurable (Y a)) (hb : ∀ a ω, Y a ω ∈ Icc lo hi)
    (hign : Ignorable μ A (measurable_const (a := ())) Y)
    (h0 : 0 < μ.real (A ⁻¹' {true})) (h1 : μ.real (A ⁻¹' {true}) < 1) :
    naiveContrast μ A Y ∈
      Icc (Manski.boundY1 μ A lo (obsOutcome A Y) - Manski.boundY0 μ A hi (obsOutcome A Y))
        (Manski.boundY1 μ A hi (obsOutcome A Y) - Manski.boundY0 μ A lo (obsOutcome A Y)) := by
  rw [← ate_eq_naiveContrast_of_ignorable hA hY
    (fun a => Manski.integrable_of_mem_Icc (hY a) (hb a)) hign h0 h1]
  exact ate_mem_manskiBounds hA hY hb

end PointTreatment

end CausalInference
