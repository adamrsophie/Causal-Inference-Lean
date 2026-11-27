/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import Mathlib.Probability.UniformOn
public import CausalInference.MissingData.Weighting

/-!
# Missing data: failure of identification without MAR

Two concrete finite models on the two point space `Bool` with the uniform measure; there is no
covariate (`X` takes values in `Unit`).

* `mnarModel`: the outcome is `Y = 1` on `true` and `Y = 0` on `false`, and it is observed
  exactly when `Y = 1` (`R = id`). So `E[Y] = 1/2`.
* `mcarModel`: the same `X` and `R`, but `Y = 1` everywhere. So `E[Y] = 1`.

## Main results

* `mnarModel_mnar`, `mnarModel_not_marMean`: the first model violates both the full and the
  mean-independence form of MAR.
* `mnarModel_completeCaseMean_ne`: its complete-case mean is `1`, not `E[Y] = 1/2`.
* `mnarModel_propensity`, `mnarModel_ipw`, `mnarModel_ipw_ne`: its response propensity is the
  constant `1/2`, and the IPW functional `E[1{R} Y / π(X)]` is `1`, not `E[Y] = 1/2`.
* `mcarModel_mcar`: the second model is MCAR.
* `observedLaw_mnarModel_eq`: the two models have the same observed-data law.
* `fullMean_not_pointIdentified`: the full-data mean is not point identified from the
  observed-data law on the class of admissible models whose response event has positive
  probability; equivalently `fullMean_not_isObservedDataFunctional`. The weaker statements on
  all admissible probability models are `fullMean_not_pointIdentified_probabilityModels` and
  `fullMean_not_isObservedDataFunctional_probabilityModels`.

## Failure of identification without positivity

Two further models on `Bool` with the uniform measure and a binary covariate `X = id`, observed
exactly when `X = true` (`R = X`):

* `posModel₀`: `Y = 0`; `posModel₁`: `Y = 1{X = false}`.
* `posModel₀_marMean`, `posModel₁_marMean`, `posModel₀_mar`, `posModel₁_mar`: both satisfy MAR,
  in the mean form and in the conditional independence form.
* `posModel₀_not_positive`: the response propensity `E[1{R} | X] = 1{X = true}` vanishes on
  `X = false`, so positivity fails, although the response probability is `1/2`.
* `observedLaw_posModel_eq`: the two models have the same observed-data law, but their full
  data means are `0` and `1/2`.
* `fullMean_not_pointIdentified_of_no_positivity`: hence the full-data mean is not point
  identified on the class of admissible MAR models with positive response probability.
-/

@[expose] public section

namespace CausalInference

namespace MissingData

namespace Counterexample

open MeasureTheory ProbabilityTheory

/-- The uniform probability measure on `Bool`. -/
noncomputable def μ₀ : Measure Bool := uniformOn Set.univ

instance : IsProbabilityMeasure μ₀ := by
  unfold μ₀
  infer_instance

theorem μ₀_singleton (b : Bool) : μ₀ {b} = 2⁻¹ := by
  rw [μ₀, uniformOn_univ]
  simp

theorem μ₀_real_singleton (b : Bool) : μ₀.real {b} = 1 / 2 := by
  simp [measureReal_def, μ₀_singleton]

theorem μ₀_singleton_ne_zero (b : Bool) : μ₀ {b} ≠ 0 := by
  simp [μ₀_singleton]

/-- Integrals against `μ₀` are averages of the two values. -/
theorem integral_μ₀ (f : Bool → ℝ) : ∫ b, f b ∂μ₀ = (f true + f false) / 2 := by
  rw [integral_fintype Integrable.of_finite]
  simp [μ₀_real_singleton]
  ring

/-- Two functions on `Bool` that agree `μ₀`-almost everywhere agree everywhere. -/
theorem eq_of_ae_eq_μ₀ {β : Type*} {f g : Bool → β} (h : f =ᵐ[μ₀] g) : f = g := by
  funext b
  by_contra hb
  apply μ₀_singleton_ne_zero b
  exact measure_mono_null (fun x hx => by rw [Set.mem_singleton_iff.mp hx]; exact hb)
    (ae_iff.mp h)

/-- The MNAR model: no covariate, `Y = 1` on `true` and `0` on `false`, and `Y` is observed
exactly when it equals `1`. -/
noncomputable def mnarModel : MissingDataModel Bool Unit where
  μ := μ₀
  X := fun _ => ()
  Y := fun b => if b then 1 else 0
  R := id

instance : IsProbabilityMeasure mnarModel.μ := inferInstanceAs (IsProbabilityMeasure μ₀)

/-- The MCAR model: the same `X` and `R` as `mnarModel`, with `Y = 1` everywhere. -/
noncomputable def mcarModel : MissingDataModel Bool Unit where
  μ := μ₀
  X := fun _ => ()
  Y := fun _ => 1
  R := id

instance : IsProbabilityMeasure mcarModel.μ := inferInstanceAs (IsProbabilityMeasure μ₀)

theorem respInd_id (b : Bool) : respInd (id : Bool → Bool) b = if b then 1 else 0 := by
  cases b <;> simp [respInd_apply]

theorem mnarModel_fullMean : mnarModel.fullMean = 1 / 2 := by
  simp [MissingDataModel.fullMean, mnarModel, integral_μ₀]

theorem mcarModel_fullMean : mcarModel.fullMean = 1 := by
  simp only [MissingDataModel.fullMean, mcarModel]
  rw [integral_μ₀]
  norm_num

/-- In the MNAR model the complete-case mean is `1`. -/
theorem mnarModel_completeCaseMean :
    completeCaseMean mnarModel.μ mnarModel.R mnarModel.Y = 1 := by
  have hpre : (mnarModel.R ⁻¹' {true}) = {true} := by ext b; simp [mnarModel]
  rw [completeCaseMean, hpre, ProbabilityTheory.cond, integral_smul_measure,
    integral_singleton]
  simp [mnarModel, ← measureReal_def, μ₀_real_singleton]

/-- In the MNAR model the complete-case mean differs from the full-data mean. -/
theorem mnarModel_completeCaseMean_ne :
    completeCaseMean mnarModel.μ mnarModel.R mnarModel.Y ≠ mnarModel.fullMean := by
  rw [mnarModel_completeCaseMean, mnarModel_fullMean]; norm_num

/-- In the MNAR model the response propensity `E[1{R} | X]` is the constant `1/2`. -/
theorem mnarModel_propensity :
    mnarModel.μ[respInd mnarModel.R | MeasurableSpace.comap mnarModel.X inferInstance] =
      fun _ => (1 / 2 : ℝ) := by
  simp only [mnarModel, MeasurableSpace.comap_const]
  rw [condExp_bot', probReal_univ]
  funext _
  simp [integral_μ₀, respInd_id]

/-- In the MNAR model the IPW functional, with the true propensity `π = 1/2`, is `1`. -/
theorem mnarModel_ipw :
    ∫ b, respInd mnarModel.R b * mnarModel.Y b / (fun _ : Unit => (1 / 2 : ℝ)) (mnarModel.X b)
      ∂mnarModel.μ = 1 := by
  simp [mnarModel, integral_μ₀, respInd_id]

/-- In the MNAR model the IPW functional with the true propensity differs from the full-data
mean. -/
theorem mnarModel_ipw_ne :
    ∫ b, respInd mnarModel.R b * mnarModel.Y b / (fun _ : Unit => (1 / 2 : ℝ)) (mnarModel.X b)
      ∂mnarModel.μ ≠ mnarModel.fullMean := by
  rw [mnarModel_ipw, mnarModel_fullMean]; norm_num

/-- The MNAR model violates the mean-independence form of MAR: given `(X, Y)` the response
indicator is `Y` itself, while given `X` it is the constant `1/2`. -/
theorem mnarModel_not_marMean :
    ¬ MARMean mnarModel.μ mnarModel.X mnarModel.Y mnarModel.R := by
  intro h
  have hm : StronglyMeasurable[MeasurableSpace.comap
      (fun b => (mnarModel.X b, mnarModel.Y b)) inferInstance] (respInd mnarModel.R) := by
    have : respInd mnarModel.R = fun b => (fun q : Unit × ℝ => q.2) (mnarModel.X b, mnarModel.Y b)
      := by funext b; simp [mnarModel, respInd_id]
    rw [this]
    exact (measurable_snd.comp (comap_measurable _)).stronglyMeasurable
  have hle : MeasurableSpace.comap (fun b => (mnarModel.X b, mnarModel.Y b)) inferInstance ≤
      (inferInstance : MeasurableSpace Bool) :=
    (measurable_of_finite _).comap_le
  rw [MARMean, condExp_of_stronglyMeasurable hle hm Integrable.of_finite,
    mnarModel_propensity] at h
  have := congrFun (eq_of_ae_eq_μ₀ h) true
  simp [mnarModel, respInd_id] at this

/-- In the MNAR model, `R` and `Y` are not conditionally independent given `X`: the model is MNAR
(the negation of the full conditional independence form of MAR). -/
theorem mnarModel_mnar :
    MNAR mnarModel.μ (measurable_const : Measurable mnarModel.X) mnarModel.R mnarModel.Y := by
  intro h
  rw [MAR, condIndepFun_iff_condExp_inter_preimage_eq_mul (measurable_of_finite _)
    (measurable_of_finite _)] at h
  have h1 := h {true} {1} (measurableSet_singleton _) (measurableSet_singleton _)
  have hX : MeasurableSpace.comap mnarModel.X (inferInstance : MeasurableSpace Unit) = ⊥ :=
    MeasurableSpace.comap_const _
  rw [hX, condExp_bot', condExp_bot', condExp_bot', probReal_univ] at h1
  have := congrFun (eq_of_ae_eq_μ₀ h1) true
  simp [mnarModel, integral_μ₀, Set.indicator] at this

/-- The model with constant outcome is MCAR. -/
theorem mcarModel_mcar : MCAR mcarModel.μ mcarModel.X mcarModel.Y mcarModel.R :=
  indepFun_const_right _ ((), 1)

/-- The two models have the same observed-data law: they differ only where `Y` is missing, so
their observed-data projections coincide. Every function on `Bool` is measurable, so both laws
are genuine push forwards of `μ₀`. -/
theorem observedLaw_mnarModel_eq : mnarModel.observedLaw = mcarModel.observedLaw := by
  refine MissingDataModel.observedLaw_eq_of_observedData_eq rfl ?_
  funext b
  cases b <;> simp [MissingDataModel.observedData, MissingDataModel.observedY, mnarModel,
    mcarModel, respInd_id]

/-- Every model on `Bool` with a probability measure is admissible: all maps out of `Bool` are
measurable. -/
theorem isAdmissible_of_bool {𝒳 : Type*} [MeasurableSpace 𝒳] [MeasurableSingletonClass 𝒳]
    {M : MissingDataModel Bool 𝒳} (h : IsProbabilityMeasure M.μ) : M.IsAdmissible :=
  ⟨h, measurable_of_finite _, measurable_of_finite _, measurable_of_finite _⟩

theorem mnarModel_isAdmissible : mnarModel.IsAdmissible :=
  isAdmissible_of_bool (inferInstanceAs (IsProbabilityMeasure μ₀))

theorem mcarModel_isAdmissible : mcarModel.IsAdmissible :=
  isAdmissible_of_bool (inferInstanceAs (IsProbabilityMeasure μ₀))

/-- The model class of all admissible missing-data models on `Bool` (with no covariate): a
probability measure and measurable variables. -/
def probabilityModels : Set (MissingDataModel Bool Unit) := {M | M.IsAdmissible}

/-- The admissible models on `Bool` (with no covariate) whose response event has positive
probability, so that some outcomes are observed. -/
def positiveResponseModels : Set (MissingDataModel Bool Unit) :=
  {M | M.IsAdmissible ∧ M.μ (M.R ⁻¹' {true}) ≠ 0}

theorem positiveResponseModels_subset : positiveResponseModels ⊆ probabilityModels :=
  fun _ hM => hM.1

theorem mnarModel_mem_positiveResponseModels : mnarModel ∈ positiveResponseModels := by
  refine ⟨mnarModel_isAdmissible, ?_⟩
  have hpre : (mnarModel.R ⁻¹' {true}) = {true} := by ext b; simp [mnarModel]
  rw [hpre]
  exact μ₀_singleton_ne_zero true

theorem mcarModel_mem_positiveResponseModels : mcarModel ∈ positiveResponseModels := by
  refine ⟨mcarModel_isAdmissible, ?_⟩
  have hpre : (mcarModel.R ⁻¹' {true}) = {true} := by ext b; simp [mcarModel]
  rw [hpre]
  exact μ₀_singleton_ne_zero true

/-- Without MAR the full-data mean is not point identified from the observed-data law, even on
admissible models whose response event has positive probability: the MNAR model and the MCAR
model have the same observed-data law but full-data means `1/2` and `1`. -/
theorem fullMean_not_pointIdentified :
    ¬ PointIdentified positiveResponseModels MissingDataModel.observedLaw
      MissingDataModel.fullMean := by
  intro h
  have := h mnarModel mnarModel_mem_positiveResponseModels mcarModel
    mcarModel_mem_positiveResponseModels observedLaw_mnarModel_eq
  rw [mnarModel_fullMean, mcarModel_fullMean] at this
  norm_num at this

/-- Equivalently, the full-data mean is not a function of the observed-data law on the class of
admissible models with positive response probability. -/
theorem fullMean_not_isObservedDataFunctional :
    ¬ IsObservedDataFunctional positiveResponseModels MissingDataModel.fullMean := by
  rw [isObservedDataFunctional_iff_pointIdentified]
  exact fullMean_not_pointIdentified

/-- Without MAR the full-data mean is not point identified from the observed-data law on the
class of all admissible probability models on `Bool`. -/
theorem fullMean_not_pointIdentified_probabilityModels :
    ¬ PointIdentified probabilityModels MissingDataModel.observedLaw
      MissingDataModel.fullMean :=
  fun h => fullMean_not_pointIdentified (h.mono positiveResponseModels_subset)

/-- Equivalently, the full-data mean is not a function of the observed-data law on the class of
all admissible probability models on `Bool`. -/
theorem fullMean_not_isObservedDataFunctional_probabilityModels :
    ¬ IsObservedDataFunctional probabilityModels MissingDataModel.fullMean := by
  rw [isObservedDataFunctional_iff_pointIdentified]
  exact fullMean_not_pointIdentified_probabilityModels

/-! ### Failure of identification without positivity -/

/-- A property that holds `μ₀`-almost everywhere holds everywhere. -/
theorem forall_of_ae_μ₀ {P : Bool → Prop} (h : ∀ᵐ b ∂μ₀, P b) (b : Bool) : P b := by
  by_contra hb
  apply μ₀_singleton_ne_zero b
  exact measure_mono_null (fun x hx => by rw [Set.mem_singleton_iff.mp hx]; exact hb)
    (ae_iff.mp h)

/-- On `Bool` with the uniform measure, if the covariate is the identity then every mechanism
satisfies the mean form of MAR: the covariate already determines the response indicator. -/
theorem marMean_of_X_id (Y : Bool → ℝ) (R : Bool → Bool) : MARMean μ₀ id Y R := by
  have hm : StronglyMeasurable[MeasurableSpace.comap id inferInstance] (respInd R) := by
    rw [MeasurableSpace.comap_id]
    exact (measurable_of_finite _).stronglyMeasurable
  have hle : MeasurableSpace.comap (fun b => (id b, Y b)) inferInstance ≤
      (inferInstance : MeasurableSpace Bool) :=
    (measurable_of_finite _).comap_le
  have hle' : MeasurableSpace.comap (id : Bool → Bool) inferInstance ≤
      (inferInstance : MeasurableSpace Bool) :=
    measurable_id.comap_le
  rw [MARMean, condExp_of_stronglyMeasurable hle (hm.mono comap_le_comap_prod)
    Integrable.of_finite, condExp_of_stronglyMeasurable hle' hm Integrable.of_finite]

/-- The first positivity model: binary covariate `X = id`, response exactly when `X = true`,
and outcome `Y = 0`. -/
noncomputable def posModel₀ : MissingDataModel Bool Bool where
  μ := μ₀
  X := id
  Y := fun _ => 0
  R := id

/-- The second positivity model: as `posModel₀`, with outcome `Y = 1{X = false}`, which is never
observed where it is nonzero. -/
noncomputable def posModel₁ : MissingDataModel Bool Bool where
  μ := μ₀
  X := id
  Y := fun b => if b then 0 else 1
  R := id

instance : IsProbabilityMeasure posModel₀.μ := inferInstanceAs (IsProbabilityMeasure μ₀)

instance : IsProbabilityMeasure posModel₁.μ := inferInstanceAs (IsProbabilityMeasure μ₀)

theorem posModel₀_marMean : MARMean posModel₀.μ posModel₀.X posModel₀.Y posModel₀.R :=
  marMean_of_X_id _ _

theorem posModel₁_marMean : MARMean posModel₁.μ posModel₁.X posModel₁.Y posModel₁.R :=
  marMean_of_X_id _ _

/-- The first positivity model satisfies the conditional independence form of MAR. -/
theorem posModel₀_mar :
    MAR posModel₀.μ (measurable_id : Measurable posModel₀.X) posModel₀.R posModel₀.Y :=
  (marMean_iff_mar measurable_id (measurable_of_finite _) measurable_id).mp posModel₀_marMean

/-- The second positivity model satisfies the conditional independence form of MAR. -/
theorem posModel₁_mar :
    MAR posModel₁.μ (measurable_id : Measurable posModel₁.X) posModel₁.R posModel₁.Y :=
  (marMean_iff_mar measurable_id (measurable_of_finite _) measurable_id).mp posModel₁_marMean

/-- In the first positivity model (and likewise in the second, which has the same `X` and `R`)
the response propensity `E[1{R} | X]` is `1{X = true}`. -/
theorem posModel₀_propensity :
    posModel₀.μ[respInd posModel₀.R | MeasurableSpace.comap posModel₀.X inferInstance] =
      respInd id := by
  have hm : StronglyMeasurable[MeasurableSpace.comap id inferInstance] (respInd (id : Bool → Bool))
      := by
    rw [MeasurableSpace.comap_id]
    exact (measurable_of_finite _).stronglyMeasurable
  exact condExp_of_stronglyMeasurable measurable_id.comap_le hm Integrable.of_finite

/-- Positivity fails in the positivity models: the response propensity vanishes on
`X = false`. -/
theorem posModel₀_not_positive : ¬ ∀ᵐ b ∂posModel₀.μ,
    0 < (posModel₀.μ[respInd posModel₀.R | MeasurableSpace.comap posModel₀.X inferInstance]) b := by
  rw [posModel₀_propensity]
  intro h
  have := forall_of_ae_μ₀ h false
  simp [respInd_apply] at this

theorem posModel₀_fullMean : posModel₀.fullMean = 0 := by
  simp [MissingDataModel.fullMean, posModel₀]

theorem posModel₁_fullMean : posModel₁.fullMean = 1 / 2 := by
  simp [MissingDataModel.fullMean, posModel₁, integral_μ₀]

/-- The two positivity models have the same observed-data law: they differ only where the
outcome is missing. -/
theorem observedLaw_posModel_eq : posModel₀.observedLaw = posModel₁.observedLaw := by
  refine MissingDataModel.observedLaw_eq_of_observedData_eq rfl ?_
  funext b
  cases b <;> simp [MissingDataModel.observedData, MissingDataModel.observedY, posModel₀,
    posModel₁, respInd_id]

/-- The admissible models on `Bool` with binary covariate, integrable outcome, the mean form of
MAR and positive response probability; the response propensity may vanish. -/
def marModelsBool : Set (MissingDataModel Bool Bool) :=
  {M | M.IsAdmissible ∧ Integrable M.Y M.μ ∧ MARMean M.μ M.X M.Y M.R ∧
    M.μ (M.R ⁻¹' {true}) ≠ 0}

theorem posModel₀_mem : posModel₀ ∈ marModelsBool := by
  refine ⟨isAdmissible_of_bool (inferInstanceAs (IsProbabilityMeasure μ₀)), Integrable.of_finite,
    posModel₀_marMean, ?_⟩
  have hpre : (posModel₀.R ⁻¹' {true}) = {true} := by ext b; simp [posModel₀]
  rw [hpre]
  exact μ₀_singleton_ne_zero true

theorem posModel₁_mem : posModel₁ ∈ marModelsBool := by
  refine ⟨isAdmissible_of_bool (inferInstanceAs (IsProbabilityMeasure μ₀)), Integrable.of_finite,
    posModel₁_marMean, ?_⟩
  have hpre : (posModel₁.R ⁻¹' {true}) = {true} := by ext b; simp [posModel₁]
  rw [hpre]
  exact μ₀_singleton_ne_zero true

/-- Without positivity of the response propensity, MAR does not identify the full-data mean:
the two positivity models satisfy MAR, have the same observed-data law and response probability
`1/2`, but full-data means `0` and `1/2`. -/
theorem fullMean_not_pointIdentified_of_no_positivity :
    ¬ PointIdentified marModelsBool MissingDataModel.observedLaw MissingDataModel.fullMean := by
  intro h
  have := h posModel₀ posModel₀_mem posModel₁ posModel₁_mem observedLaw_posModel_eq
  rw [posModel₀_fullMean, posModel₁_fullMean] at this
  norm_num at this

/-- Equivalently, without positivity the full-data mean is not a function of the observed-data
law on the class of admissible MAR models. -/
theorem fullMean_not_isObservedDataFunctional_of_no_positivity :
    ¬ IsObservedDataFunctional marModelsBool MissingDataModel.fullMean := by
  rw [isObservedDataFunctional_iff_pointIdentified]
  exact fullMean_not_pointIdentified_of_no_positivity

end Counterexample

end MissingData

end CausalInference
