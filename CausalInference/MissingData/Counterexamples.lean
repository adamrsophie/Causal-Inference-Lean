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
  observed-data law on the class of models with a probability measure; equivalently
  `fullMean_not_isObservedDataFunctional`.
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

/-- The model class of all missing-data models on `Bool` with a probability measure. -/
def probabilityModels : Set (MissingDataModel Bool Unit) := {M | IsProbabilityMeasure M.μ}

/-- Without MAR the full-data mean is not point identified from the observed-data law: the MNAR
model and the MCAR model have the same observed-data law but full-data means `1/2` and `1`. -/
theorem fullMean_not_pointIdentified :
    ¬ PointIdentified probabilityModels MissingDataModel.observedLaw
      MissingDataModel.fullMean := by
  intro h
  have := h mnarModel (show IsProbabilityMeasure μ₀ from inferInstance) mcarModel
    (show IsProbabilityMeasure μ₀ from inferInstance) observedLaw_mnarModel_eq
  rw [mnarModel_fullMean, mcarModel_fullMean] at this
  norm_num at this

/-- Equivalently, the full-data mean is not a function of the observed-data law on the class of
models with a probability measure. -/
theorem fullMean_not_isObservedDataFunctional :
    ¬ IsObservedDataFunctional probabilityModels MissingDataModel.fullMean := by
  rw [isObservedDataFunctional_iff_pointIdentified]
  exact fullMean_not_pointIdentified

end Counterexample

end MissingData

end CausalInference
