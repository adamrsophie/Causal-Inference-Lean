/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.Transport.Formula
public import CausalInference.MissingData.Identification
public import CausalInference.PartialIdentification.IdentifiedSet

/-!
# Transport: transportability as identification

A target estimand is **transportable** from a source population to a target population when it
is point identified (`PointIdentified`) from the law of the data observed in the source study,
`(X₁, A, Y)`, together with the law of the covariates in the target, `X₂` (Pearl and
Bareinboim 2011). Nothing else about the target is observed.

On the class of models satisfying conditional transportability of the mean of arm `a`, the
target mean `E₂[Y₂(a)]` is the value of an explicit functional of these two laws
(`targetMean_eq_transportFunctional`), so it is transportable (`pointIdentified_targetMean`).
The functional is the inverse probability weighting functional of the missing data layer
(`ipwFunctional`) applied to the source law pushed forward by
`(x, b, y) ↦ (x, 1{b = a}, 1{b = a} w(x) y)`, with `w` the density ratio of the target
covariate law to the covariate marginal of the source law. The proof views the arm of the
source study as a missing data model whose full outcome is `w(X₁) Y₁(a)`.

A **directly transportable** estimand takes the same value in both populations; if it is
identified in the source from the source law alone, it is transportable
(`pointIdentified_of_directlyTransportable`).

## Main definitions

* `TransportModel Ω₁ Ω₂ 𝒳`: a source study and a target population.
* `TransportModel.observed`: the pair (source law of `(X₁, A, Y)`, target law of `X₂`).
* `TransportModel.IsConditionallyTransportable M a`: the assumptions of conditional
  transportability for arm `a`.
* `transportFunctional a`: the identifying functional.

## Main results

* `targetMean_eq_transportFunctional`, `pointIdentified_targetMean`.
* `pointIdentified_of_directlyTransportable`.

## References

* J. Pearl and E. Bareinboim, *Transportability of causal and statistical relations: a formal
  approach*, Proceedings of the AAAI Conference on Artificial Intelligence (2011).
-/

@[expose] public section

namespace CausalInference

namespace Transport

open MeasureTheory ProbabilityTheory MissingData PointTreatment

/-- A **transport model**: a source study `(μ₁, X₁, A, Y₁)` of a point treatment, with
potential outcomes `Y₁`, and a target population `(μ₂, X₂, Y₂)` with potential outcomes `Y₂`,
on a common covariate space. -/
structure TransportModel (Ω₁ Ω₂ 𝒳 : Type*) [MeasurableSpace Ω₁] [MeasurableSpace Ω₂] where
  /-- The source measure. -/
  μ₁ : Measure Ω₁
  /-- The source covariates. -/
  X₁ : Ω₁ → 𝒳
  /-- The treatment in the source study. -/
  A : Ω₁ → Bool
  /-- The potential outcomes in the source. -/
  Y₁ : Bool → Ω₁ → ℝ
  /-- The target measure. -/
  μ₂ : Measure Ω₂
  /-- The target covariates. -/
  X₂ : Ω₂ → 𝒳
  /-- The potential outcomes in the target. -/
  Y₂ : Bool → Ω₂ → ℝ

namespace TransportModel

variable {Ω₁ Ω₂ 𝒳 : Type*} [MeasurableSpace Ω₁] [MeasurableSpace Ω₂] [MeasurableSpace 𝒳]

/-- The law of the data of the source study, `(X₁, A, Y)` with `Y = Y₁(A)`. -/
noncomputable def sourceLaw (M : TransportModel Ω₁ Ω₂ 𝒳) : Measure (𝒳 × Bool × ℝ) :=
  M.μ₁.map fun ω => (M.X₁ ω, M.A ω, obsOutcome M.A M.Y₁ ω)

/-- The law of the target covariates. -/
noncomputable def targetCovLaw (M : TransportModel Ω₁ Ω₂ 𝒳) : Measure 𝒳 := M.μ₂.map M.X₂

/-- What is observed: the source law and the target covariate law. -/
noncomputable def observed (M : TransportModel Ω₁ Ω₂ 𝒳) :
    Measure (𝒳 × Bool × ℝ) × Measure 𝒳 :=
  (M.sourceLaw, M.targetCovLaw)

/-- The target mean of arm `a`, `E₂[Y₂(a)]`. -/
noncomputable def targetMean (M : TransportModel Ω₁ Ω₂ 𝒳) (a : Bool) : ℝ :=
  ∫ ω, M.Y₂ a ω ∂M.μ₂

/-- The assumptions of **conditional transportability** of the mean of arm `a`: probability
measures, measurable variables, integrable potential outcomes of arm `a` in both populations,
exchangeability in the source in indicator form with positivity of the arm, structural
invariance, overlap of the covariate laws, and integrability of `w(X₁) Y₁(a)` in the
source. -/
structure IsConditionallyTransportable (M : TransportModel Ω₁ Ω₂ 𝒳) (a : Bool) : Prop where
  /-- The source measure is a probability measure. -/
  isProbabilityMeasure_μ₁ : IsProbabilityMeasure M.μ₁
  /-- The target measure is a probability measure. -/
  isProbabilityMeasure_μ₂ : IsProbabilityMeasure M.μ₂
  /-- The source covariates are measurable. -/
  measurable_X₁ : Measurable M.X₁
  /-- The treatment is measurable. -/
  measurable_A : Measurable M.A
  /-- The source potential outcomes are measurable. -/
  measurable_Y₁ : ∀ b, Measurable (M.Y₁ b)
  /-- The target covariates are measurable. -/
  measurable_X₂ : Measurable M.X₂
  /-- The source potential outcome of arm `a` is integrable. -/
  integrable_Y₁ : Integrable (M.Y₁ a) M.μ₁
  /-- The target potential outcome of arm `a` is integrable. -/
  integrable_Y₂ : Integrable (M.Y₂ a) M.μ₂
  /-- Exchangeability in the source, in indicator form: `E[1{A = a} | X₁, Y₁(a)] =
  E[1{A = a} | X₁]`. -/
  marMean : MARMean M.μ₁ M.X₁ (M.Y₁ a) (arm M.A a)
  /-- Positivity of the arm in the source. -/
  pos : ∀ᵐ ω ∂M.μ₁,
    0 < (M.μ₁[respInd (arm M.A a) | MeasurableSpace.comap M.X₁ inferInstance]) ω
  /-- Structural invariance of the conditional mean of `Y(a)`. -/
  structurallyInvariant : StructurallyInvariant M.μ₁ M.X₁ (M.Y₁ a) M.μ₂ M.X₂ (M.Y₂ a)
  /-- Overlap: the target covariate law is absolutely continuous with respect to the source
  covariate law. -/
  overlap : M.μ₂.map M.X₂ ≪ M.μ₁.map M.X₁
  /-- The reweighted source potential outcome is integrable. -/
  integrable_weight : Integrable (fun ω => densityRatio M.μ₁ M.X₁ M.μ₂ M.X₂ (M.X₁ ω) *
    M.Y₁ a ω) M.μ₁

end TransportModel

variable {Ω₁ Ω₂ 𝒳 : Type*} [MeasurableSpace Ω₁] [MeasurableSpace Ω₂] [MeasurableSpace 𝒳]

/-- The map `(x, b, y) ↦ (x, 1{b = a}, 1{b = a} w(x) y)` that turns the source law into the
observed law of the missing data model of arm `a` with full outcome `w(X₁) Y₁(a)`. -/
noncomputable def transportMap (a : Bool) (w : 𝒳 → ℝ) (q : 𝒳 × Bool × ℝ) : 𝒳 × Bool × ℝ :=
  (q.1, q.2.1 == a, (if q.2.1 = a then 1 else 0) * (w q.1 * q.2.2))

theorem measurable_transportMap (a : Bool) {w : 𝒳 → ℝ} (hw : Measurable w) :
    Measurable (transportMap a w) := by
  have hb : Measurable fun q : 𝒳 × Bool × ℝ => q.2.1 == a :=
    (Measurable.of_discrete (f := fun b : Bool => b == a)).comp measurable_snd.fst
  have hi : Measurable fun q : 𝒳 × Bool × ℝ => if q.2.1 = a then (1 : ℝ) else 0 :=
    (Measurable.of_discrete (f := fun b : Bool => if b = a then (1 : ℝ) else 0)).comp
      measurable_snd.fst
  exact measurable_fst.prodMk (hb.prodMk (hi.mul ((hw.comp measurable_fst).mul
    measurable_snd.snd)))

/-- The **identifying functional of transport** for arm `a`: from the source law `P` and the
target covariate law `Q`, with `w = (dQ / d(P ∘ fst⁻¹))` as a real function, the inverse
probability weighting functional of `P` pushed forward by `transportMap a w`. -/
noncomputable def transportFunctional (a : Bool) (o : Measure (𝒳 × Bool × ℝ) × Measure 𝒳) :
    ℝ :=
  ipwFunctional (o.1.map (transportMap a fun x => (o.2.rnDeriv (o.1.map Prod.fst) x).toReal))

namespace TransportModel

/-- The arm `a` of the source study as a missing data model with full outcome `w(X₁) Y₁(a)`
and response indicator `{A = a}`. -/
noncomputable def weightedArmModel (M : TransportModel Ω₁ Ω₂ 𝒳) (a : Bool) :
    MissingDataModel Ω₁ 𝒳 :=
  ⟨M.μ₁, M.X₁, fun ω => densityRatio M.μ₁ M.X₁ M.μ₂ M.X₂ (M.X₁ ω) * M.Y₁ a ω, arm M.A a⟩

/-- **The target mean as a functional of what is observed.** Under conditional
transportability of arm `a`, `E₂[Y₂(a)] = transportFunctional a (source law, target covariate
law)`. -/
theorem targetMean_eq_transportFunctional {M : TransportModel Ω₁ Ω₂ 𝒳} {a : Bool}
    (hM : M.IsConditionallyTransportable a) :
    M.targetMean a = transportFunctional a M.observed := by
  have := hM.isProbabilityMeasure_μ₁
  have := hM.isProbabilityMeasure_μ₂
  have hX₁ := hM.measurable_X₁
  have hA := hM.measurable_A
  set w := densityRatio M.μ₁ M.X₁ M.μ₂ M.X₂
  have hw : Measurable w := measurable_densityRatio _ _ _ _
  obtain ⟨g, hg, Hsrc, Htgt⟩ := hM.structurallyInvariant
  -- the target mean is the source mean of `w(X₁) Y₁(a)`
  have hmean : M.targetMean a = (M.weightedArmModel a).fullMean := by
    rw [targetMean, (integral_target_eq_integral_common hM.measurable_X₂ hM.integrable_Y₂ hg
      Htgt).2, integral_densityRatio_mul hX₁ hM.overlap hg,
      integral_densityRatio_mul_common hX₁ hM.integrable_Y₁ Hsrc hM.integrable_weight]
    rfl
  -- the weighted arm model satisfies MAR with positivity
  have hle : MeasurableSpace.comap (fun ω => (M.X₁ ω, w (M.X₁ ω) * M.Y₁ a ω)) inferInstance ≤
      MeasurableSpace.comap (fun ω => (M.X₁ ω, M.Y₁ a ω)) inferInstance :=
    ((measurable_fst.prodMk ((hw.comp measurable_fst).mul measurable_snd)).comp
      (comap_measurable fun ω => (M.X₁ ω, M.Y₁ a ω))).comap_le
  have hmem : M.weightedArmModel a ∈ marPositiveModels :=
    ⟨⟨hM.isProbabilityMeasure_μ₁, hX₁, measurable_arm hA a,
      (hw.comp hX₁).mul (hM.measurable_Y₁ a)⟩, hM.integrable_weight,
      marMean_of_comap_le hM.marMean hX₁ (hM.measurable_Y₁ a) hle, hM.pos⟩
  -- its observed law is the source law pushed forward by `transportMap a w`
  have hsrc : Measurable fun ω => (M.X₁ ω, M.A ω, obsOutcome M.A M.Y₁ ω) :=
    hX₁.prodMk (hA.prodMk (measurable_obsOutcome hA hM.measurable_Y₁))
  have hfst : M.sourceLaw.map Prod.fst = M.μ₁.map M.X₁ := by
    rw [sourceLaw, Measure.map_map measurable_fst hsrc]
    rfl
  have hlaw : (M.weightedArmModel a).observedLaw = M.sourceLaw.map (transportMap a w) := by
    rw [MissingDataModel.observedLaw, sourceLaw, Measure.map_map (measurable_transportMap a hw)
      hsrc]
    refine congrArg (Measure.map · M.μ₁) (funext fun ω => ?_)
    simp only [MissingDataModel.observedData, MissingDataModel.observedY, weightedArmModel,
      Function.comp_apply, transportMap, respInd_arm_apply]
    refine Prod.ext rfl (Prod.ext rfl ?_)
    by_cases h : M.A ω = a
    · simp [h, obsOutcome, w]
    · simp [h]
  rw [hmean, fullMean_eq_ipwFunctional hmem, hlaw, transportFunctional, observed, hfst]
  rfl

end TransportModel

open TransportModel

/-- **The target mean is transportable**: on the models satisfying conditional
transportability of arm `a`, the target mean `E₂[Y₂(a)]` is point identified from the source
law and the target covariate law. -/
theorem pointIdentified_targetMean (a : Bool) :
    PointIdentified {M : TransportModel Ω₁ Ω₂ 𝒳 | M.IsConditionallyTransportable a}
      TransportModel.observed (fun M => M.targetMean a) :=
  pointIdentified_iff_exists_factor.2
    ⟨transportFunctional a, fun _ hM => targetMean_eq_transportFunctional hM⟩

/-- **Directly transportable estimands.** If a source estimand `ψ₁` is point identified on a
class from the source law alone, and a target estimand `ψ₂` takes the same value on every model
of the class, then `ψ₂` is point identified from the source law and the target covariate
law. -/
theorem pointIdentified_of_directlyTransportable {K : Set (TransportModel Ω₁ Ω₂ 𝒳)}
    {ψ₁ ψ₂ : TransportModel Ω₁ Ω₂ 𝒳 → ℝ}
    (h₁ : PointIdentified K TransportModel.sourceLaw ψ₁) (hdir : ∀ M ∈ K, ψ₂ M = ψ₁ M) :
    PointIdentified K TransportModel.observed ψ₂ := by
  intro M hM M' hM' hobs
  rw [hdir M hM, hdir M' hM']
  exact h₁ M hM M' hM' (congrArg Prod.fst hobs)

end Transport

end CausalInference
