/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.Probability.ConditionalProbability
public import CausalInference.PartialIdentification.IdentifiedSet

/-!
# Missing data: models, the observed-data projection, observed-data functionals

The basic setting of missing-data theory in the sense of Rubin (1976).

## Setting

A measurable space `Ω` with a measure `μ` (a probability measure in applications), a full-data
outcome `Y : Ω → ℝ`, an always observed covariate `X : Ω → 𝒳`, and a response indicator
`R : Ω → Bool`, where `R ω = true` means that `Y ω` is observed. The analyst sees only the
observed data `(X, R, R · Y)`: the outcome is replaced by `0` when it is missing, and the
indicator `R` records whether the recorded `0` is a genuine value.

## Main definitions

* `MissingDataModel Ω 𝒳`: a measure together with `X`, `Y` and `R`.
* `MissingDataModel.IsAdmissible`: the model is a probability model with measurable `X`, `R`
  and `Y`; then the observed-data projection is measurable and the observed-data law is a
  genuine push forward. Every statement that interprets the observed-data law is restricted to
  admissible models.
* `respInd R`: the real indicator of the response event `{R = true}`.
* `MissingDataModel.observedData`: the observed-data projection `ω ↦ (X ω, R ω, R ω · Y ω)`.
* `MissingDataModel.observedLaw`: the law of the observed data (the push forward of `μ`).
* `MissingDataModel.fullMean`: the full-data mean `E[Y]`.
* `completeCaseMean μ R Y`: the complete-case mean `E[Y | R = true]`.
* `IsObservedDataFunctional S θ`: on the model class `S`, the functional `θ` is a function of
  the observed-data law.

## Main results

* `isObservedDataFunctional_iff_pointIdentified`: a functional is a function of the observed-data
  law on `S` if and only if it is point identified on `S` from the observed-data law, in the
  sense of `CausalInference.PointIdentified`.
* `MissingDataModel.IsAdmissible.measurable_observedData`: on an admissible model the
  observed-data projection is measurable, and the observed-data law is a probability measure.
* `MissingDataModel.completeCaseMean_eq_observedLaw`: on an admissible model with a response
  event of positive probability on which `Y` is integrable, the complete-case mean is computed
  from the observed-data law alone; hence `isObservedDataFunctional_completeCaseMean`.

## References

* D. B. Rubin, *Inference and missing data*, Biometrika 63 (1976).
* R. J. A. Little and D. B. Rubin, *Statistical Analysis with Missing Data*, Wiley.
-/

@[expose] public section

namespace CausalInference

namespace MissingData

open MeasureTheory ProbabilityTheory

/-- The real indicator of the response event `{R = true}`: it is `1` where the outcome is
observed and `0` where it is missing. -/
noncomputable def respInd {Ω : Type*} (R : Ω → Bool) : Ω → ℝ :=
  (R ⁻¹' {true}).indicator 1

theorem respInd_apply {Ω : Type*} (R : Ω → Bool) (ω : Ω) :
    respInd R ω = if R ω = true then 1 else 0 := by
  by_cases h : R ω = true <;> simp [respInd, Set.indicator, h]

theorem respInd_nonneg {Ω : Type*} (R : Ω → Bool) (ω : Ω) : 0 ≤ respInd R ω := by
  rw [respInd_apply]; split_ifs <;> norm_num

theorem respInd_le_one {Ω : Type*} (R : Ω → Bool) (ω : Ω) : respInd R ω ≤ 1 := by
  rw [respInd_apply]; split_ifs <;> norm_num

theorem measurable_respInd {Ω : Type*} [MeasurableSpace Ω] {R : Ω → Bool} (hR : Measurable R) :
    Measurable (respInd R) :=
  measurable_const.indicator (hR (measurableSet_singleton true))

/-- A missing-data model on the sample space `Ω` with covariate space `𝒳`: a measure `μ`, an
always observed covariate `X`, a full-data outcome `Y`, and a response indicator `R`
(`R ω = true` means `Y ω` is observed). -/
structure MissingDataModel (Ω 𝒳 : Type*) [MeasurableSpace Ω] where
  /-- The underlying measure (a probability measure in applications). -/
  μ : Measure Ω
  /-- The always observed covariate. -/
  X : Ω → 𝒳
  /-- The full-data outcome. -/
  Y : Ω → ℝ
  /-- The response indicator: `true` when `Y` is observed. -/
  R : Ω → Bool

namespace MissingDataModel

variable {Ω 𝒳 : Type*} [MeasurableSpace Ω] [MeasurableSpace 𝒳]

/-- The observed outcome `R · Y`: the outcome where it is observed and `0` where it is missing. -/
noncomputable def observedY (M : MissingDataModel Ω 𝒳) : Ω → ℝ :=
  fun ω => respInd M.R ω * M.Y ω

/-- The observed-data projection `ω ↦ (X ω, R ω, R ω · Y ω)`. -/
noncomputable def observedData (M : MissingDataModel Ω 𝒳) : Ω → 𝒳 × Bool × ℝ :=
  fun ω => (M.X ω, M.R ω, M.observedY ω)

/-- The observed-data law: the law of `(X, R, R · Y)` under `μ`.

It is the law of the observed data only when the observed-data projection is almost everywhere
measurable, as it is on an admissible model (`IsAdmissible`). Otherwise Mathlib's
`Measure.map` returns `0` for the zero measure and an arbitrary Dirac mass for a nonzero
measure, which carries no information about the model. For example, on a two point probability
space with the trivial σ-algebra, constant `X` and `Y` and a response indicator that separates
the two points, the projection is not almost everywhere measurable. -/
noncomputable def observedLaw (M : MissingDataModel Ω 𝒳) : Measure (𝒳 × Bool × ℝ) :=
  M.μ.map M.observedData

/-- The full-data mean `E[Y]`, the usual target of a missing-data analysis. It is the
expectation of `Y` only when `Y` is integrable; otherwise the Bochner integral is `0` by
convention. The identification theorems that interpret it assume `Integrable M.Y M.μ` (on a
finite sample space with a finite measure this holds automatically). -/
noncomputable def fullMean (M : MissingDataModel Ω 𝒳) : ℝ :=
  ∫ ω, M.Y ω ∂M.μ

omit [MeasurableSpace 𝒳] in
theorem observedY_of_true (M : MissingDataModel Ω 𝒳) {ω : Ω} (h : M.R ω = true) :
    M.observedY ω = M.Y ω := by
  simp [observedY, respInd_apply, h]

theorem measurable_observedData (M : MissingDataModel Ω 𝒳) (hX : Measurable M.X)
    (hR : Measurable M.R) (hY : Measurable M.Y) : Measurable M.observedData :=
  hX.prodMk (hR.prodMk ((measurable_respInd hR).mul hY))

/-- A missing-data model is admissible when its measure is a probability measure and `X`, `R`
and `Y` are measurable. Then the observed-data projection is measurable
(`IsAdmissible.measurable_observedData`), so the observed-data law is the genuine law of the
observed data. -/
structure IsAdmissible (M : MissingDataModel Ω 𝒳) : Prop where
  /-- The underlying measure is a probability measure. -/
  isProbabilityMeasure : IsProbabilityMeasure M.μ
  /-- The covariate is measurable. -/
  measurable_X : Measurable M.X
  /-- The response indicator is measurable. -/
  measurable_R : Measurable M.R
  /-- The outcome is measurable. -/
  measurable_Y : Measurable M.Y

/-- On an admissible model the observed-data projection is measurable. -/
theorem IsAdmissible.measurable_observedData {M : MissingDataModel Ω 𝒳} (hM : M.IsAdmissible) :
    Measurable M.observedData :=
  M.measurable_observedData hM.measurable_X hM.measurable_R hM.measurable_Y

/-- On an admissible model the observed-data projection is almost everywhere measurable. -/
theorem IsAdmissible.aemeasurable_observedData {M : MissingDataModel Ω 𝒳}
    (hM : M.IsAdmissible) : AEMeasurable M.observedData M.μ :=
  hM.measurable_observedData.aemeasurable

/-- On an admissible model the observed-data law is a probability measure. -/
theorem IsAdmissible.isProbabilityMeasure_observedLaw {M : MissingDataModel Ω 𝒳}
    (hM : M.IsAdmissible) : IsProbabilityMeasure M.observedLaw :=
  (Measure.isProbabilityMeasure_map_iff hM.aemeasurable_observedData).mpr hM.isProbabilityMeasure

/-- Two models whose observed-data projections agree pointwise, on the same measure, have the
same observed-data law. -/
theorem observedLaw_eq_of_observedData_eq {M M' : MissingDataModel Ω 𝒳} (hμ : M.μ = M'.μ)
    (h : M.observedData = M'.observedData) : M.observedLaw = M'.observedLaw := by
  rw [observedLaw, observedLaw, hμ, h]

end MissingDataModel

/-- The complete-case mean `E[Y | R = true]`: the mean of `Y` under `μ` conditioned on the
response event. It is the conditional mean only when `μ` is finite, `μ {R = true} ≠ 0` and `Y`
is integrable on the response event; otherwise the conditional measure is `0` or the integral
is `0` by convention. -/
noncomputable def completeCaseMean {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (R : Ω → Bool) (Y : Ω → ℝ) : ℝ :=
  ∫ ω, Y ω ∂μ[|R ⁻¹' {true}]

variable {Ω 𝒳 : Type*} [MeasurableSpace Ω] [MeasurableSpace 𝒳]

/-- On the model class `S`, the real functional `θ` is a function of the observed-data law:
some `G` on laws of `(X, R, R · Y)` satisfies `θ M = G (law of the observed data of M)` for
every `M ∈ S`.

The observed-data law is meaningful only on admissible models (`MissingDataModel.IsAdmissible`),
so the classes `S` used with this predicate in this library consist of admissible models. -/
def IsObservedDataFunctional (S : Set (MissingDataModel Ω 𝒳))
    (θ : MissingDataModel Ω 𝒳 → ℝ) : Prop :=
  ∃ G : Measure (𝒳 × Bool × ℝ) → ℝ, ∀ M ∈ S, θ M = G M.observedLaw

/-- A functional is a function of the observed-data law on `S` exactly when it is point
identified on `S` from the observed-data law: models of `S` with the same observed-data law
have the same value. -/
theorem isObservedDataFunctional_iff_pointIdentified {S : Set (MissingDataModel Ω 𝒳)}
    {θ : MissingDataModel Ω 𝒳 → ℝ} :
    IsObservedDataFunctional S θ ↔ PointIdentified S MissingDataModel.observedLaw θ :=
  pointIdentified_iff_exists_factor.symm

/-- The complete-case mean depends on the model only through the observed-data law: on an
admissible model whose response event has positive probability and on which `Y` is integrable,
it equals the mean of the third coordinate under the observed-data law conditioned on
`R = true`. Under the same hypotheses that conditioned law is a probability measure under which
the third coordinate is integrable, so both sides are genuine conditional means. -/
theorem MissingDataModel.completeCaseMean_eq_observedLaw (M : MissingDataModel Ω 𝒳)
    (hM : M.IsAdmissible) (hpos : M.μ (M.R ⁻¹' {true}) ≠ 0)
    (hint : IntegrableOn M.Y (M.R ⁻¹' {true}) M.μ) :
    completeCaseMean M.μ M.R M.Y =
        ∫ p, p.2.2 ∂M.observedLaw[|{p : 𝒳 × Bool × ℝ | p.2.1 = true}] ∧
      IsProbabilityMeasure M.observedLaw[|{p : 𝒳 × Bool × ℝ | p.2.1 = true}] ∧
      Integrable (fun p : 𝒳 × Bool × ℝ => p.2.2)
        M.observedLaw[|{p : 𝒳 × Bool × ℝ | p.2.1 = true}] := by
  have := hM.isProbabilityMeasure
  have := hM.isProbabilityMeasure_observedLaw
  have hR := hM.measurable_R
  have hO := hM.measurable_observedData
  have hT : MeasurableSet {p : 𝒳 × Bool × ℝ | p.2.1 = true} :=
    measurable_snd.fst (measurableSet_singleton true)
  have hpre : M.observedData ⁻¹' {p : 𝒳 × Bool × ℝ | p.2.1 = true} = M.R ⁻¹' {true} := rfl
  have hS : MeasurableSet (M.R ⁻¹' {true}) := hR (measurableSet_singleton true)
  have hlaw : M.observedLaw {p : 𝒳 × Bool × ℝ | p.2.1 = true} = M.μ (M.R ⁻¹' {true}) := by
    rw [MissingDataModel.observedLaw, Measure.map_apply hO hT, hpre]
  refine ⟨?_, cond_isProbabilityMeasure (hlaw ▸ hpos), ?_⟩
  · rw [completeCaseMean, MissingDataModel.observedLaw, ProbabilityTheory.cond,
      ProbabilityTheory.cond, Measure.restrict_map hO hT,
      Measure.map_apply hO hT, hpre, integral_smul_measure, integral_smul_measure,
      integral_map hO.aemeasurable (by fun_prop)]
    congr 1
    refine setIntegral_congr_fun hS fun ω hω => ?_
    exact (M.observedY_of_true hω).symm
  · rw [ProbabilityTheory.cond]
    refine Integrable.smul_measure ?_ (ENNReal.inv_ne_top.mpr (hlaw ▸ hpos))
    rw [MissingDataModel.observedLaw, Measure.restrict_map hO hT, hpre,
      integrable_map_measure (by fun_prop) hO.aemeasurable]
    refine hint.congr_fun (fun ω hω => ?_) hS
    exact (M.observedY_of_true hω).symm

/-- The complete-case mean is a function of the observed-data law on every class of admissible
models whose response event has positive probability and on which `Y` is integrable over the
response event. -/
theorem isObservedDataFunctional_completeCaseMean {S : Set (MissingDataModel Ω 𝒳)}
    (hS : ∀ M ∈ S, M.IsAdmissible ∧ M.μ (M.R ⁻¹' {true}) ≠ 0 ∧
      IntegrableOn M.Y (M.R ⁻¹' {true}) M.μ) :
    IsObservedDataFunctional S (fun M => completeCaseMean M.μ M.R M.Y) :=
  ⟨fun ν => ∫ p, p.2.2 ∂ν[|{p : 𝒳 × Bool × ℝ | p.2.1 = true}], fun M hM =>
    (M.completeCaseMean_eq_observedLaw (hS M hM).1 (hS M hM).2.1 (hS M hM).2.2).1⟩

end MissingData

end CausalInference
