/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.PopulationAdjustment.DensityRatio
public import CausalInference.PointTreatment.Weighting

/-!
# Inverse treatment probabilities in the transport weights

A source study with covariates `X₁`, treatment `A` and propensity score `e` is reweighted to a
target population with the density ratio `w = dP*_X / dP_X` (`Transport.densityRatio`). When the
probability of the arm `a` depends on the covariates, the weight of a unit of arm `a` is
`w(X₁) / π_a(X₁)`, the density ratio times the inverse probability weight
`1{A = a} / π_a(X₁)` (`PointTreatment.ipwWeight`).

* **Pulling a function of the covariates out of the arm indicator**
  (`integral_respInd_arm_mul_comp`): `E[1{A = a} f(X₁)] = E[π_a(X₁) f(X₁)]` for every measurable
  `f`, with no integrability hypothesis (both sides are integrable together).
* **The weights have mean one** (`integral_densityRatio_mul_ipwWeight`): under positivity and
  overlap, `w(X₁) 1{A = a} / π_a(X₁)` is integrable and has mean `1`. The integrability is
  derived.
* **The self normalized transport identity** (`hajek_transport_eq_targetMean`): under the
  assumptions of the transport formula (`Transport.integral_target_eq_transport`) the ratio
  `E[w 1{A = a} Y / π_a] / E[w 1{A = a} / π_a]` is the target mean.
* **The population weighted arm mean with inverse probability weights**
  (`lawWeightedArmMean_div_armProb_eq_targetMean`): under conditional transportability of the arm
  `a` and any propensity score `e`, every weight function equal almost everywhere to a nonzero
  multiple of `w / π_a` gives `lawWeightedArmMean` equal to the target mean. This extends
  `lawWeightedArmMean_sourceLaw_eq_targetMean`, which needs a constant assignment probability.
* **Omitting the inverse probabilities gives the wrong limit** (`ipwDesign_results`): a source
  with a binary covariate `x`, equally likely, assignment probability `1/4` at `x = false` and
  `3/4` at `x = true`, outcome `Y(t) = 1{x}`, and the target equal to the source. The arm is
  conditionally transportable, the weighted arm mean with weights `1/π_true(x)` is the target
  mean `1/2`, and the weighted arm mean with the density ratio alone is `3/4`.

## Main definitions

* `ipwDesignScore`, `ipwDesignLaw`, `ipwDesignModel`.

## Main results

* `integral_respInd_arm_mul_comp`, `integral_densityRatio_mul_ipwWeight`,
  `hajek_transport_eq_targetMean`, `lawWeightedArmMean_div_armProb_eq_targetMean`.
* `lawWeightedArmMean_ipwDesign`, `ipwDesign_results`.
-/

@[expose] public section

namespace CausalInference

namespace PopulationAdjustment

open MeasureTheory ProbabilityTheory MissingData PointTreatment Transport EffectMeasure
open scoped ENNReal

/-! ### Population identities -/

section Identities

variable {Ω₁ Ω₂ 𝒳 : Type*} {mΩ₁ : MeasurableSpace Ω₁} {mΩ₂ : MeasurableSpace Ω₂}
  [MeasurableSpace 𝒳] {μ₁ : Measure Ω₁} {μ₂ : Measure Ω₂} {X₁ : Ω₁ → 𝒳} {X₂ : Ω₂ → 𝒳}
  {A : Ω₁ → Bool} {e : 𝒳 → ℝ}

/-- **A function of the covariates comes out of the arm indicator**: if `e` is the propensity
score, then for every measurable `f`, `E[1{A = a} f(X₁)] = E[π_a(X₁) f(X₁)]`. No integrability
is assumed: the two integrands are integrable together (`integrable_respInd_arm_mul_iff`). -/
theorem integral_respInd_arm_mul_comp [IsFiniteMeasure μ₁] (hX₁ : Measurable X₁)
    (hA : Measurable A) (hps : IsPropensityScore μ₁ A X₁ e) (a : Bool) {f : 𝒳 → ℝ}
    (hf : Measurable f) :
    ∫ ω, respInd (arm A a) ω * f (X₁ ω) ∂μ₁ = ∫ ω, armProb e a (X₁ ω) * f (X₁ ω) ∂μ₁ := by
  have hfm : StronglyMeasurable[MeasurableSpace.comap X₁ inferInstance] (fun ω => f (X₁ ω)) :=
    (hf.comp (comap_measurable X₁)).stronglyMeasurable
  by_cases hi : Integrable (fun ω => respInd (arm A a) ω * f (X₁ ω)) μ₁
  · exact (integral_mul_eq_of_condExp_eq hX₁.comap_le (integrable_respInd (measurable_arm hA a))
      hfm hi (hps.condExp_arm hX₁ hA a)).2
  · rw [integral_undef hi,
      integral_undef (mt (integrable_respInd_arm_mul_iff hX₁ hA hps a hf).2 hi)]

/-- **The transport weights with inverse treatment probabilities have mean one.** If `e` is the
propensity score, `π_a(X₁) > 0` almost surely, the target law is a probability law and
`P*_X ≪ P_X`, then `w(X₁) 1{A = a} / π_a(X₁)` is integrable and `E[w(X₁) 1{A = a} / π_a(X₁)] = 1`.
-/
theorem integral_densityRatio_mul_ipwWeight [IsFiniteMeasure μ₁] [IsProbabilityMeasure μ₂]
    (hX₁ : Measurable X₁) (hA : Measurable A) (hps : IsPropensityScore μ₁ A X₁ e) (a : Bool)
    (hpos : ∀ᵐ ω ∂μ₁, 0 < armProb e a (X₁ ω)) (hov : μ₂.map X₂ ≪ μ₁.map X₁) :
    Integrable (fun ω => densityRatio μ₁ X₁ μ₂ X₂ (X₁ ω) * ipwWeight A X₁ e a ω) μ₁ ∧
      ∫ ω, densityRatio μ₁ X₁ μ₂ X₂ (X₁ ω) * ipwWeight A X₁ e a ω ∂μ₁ = 1 := by
  set w := densityRatio μ₁ X₁ μ₂ X₂
  have hwm := measurable_densityRatio μ₁ X₁ μ₂ X₂
  have hfm : Measurable fun x => w x / armProb e a x := hwm.div (measurable_armProb hps.1 a)
  have e1 : (fun ω => w (X₁ ω) * ipwWeight A X₁ e a ω) =
      fun ω => respInd (arm A a) ω * (w (X₁ ω) / armProb e a (X₁ ω)) := by
    funext ω; simp only [ipwWeight]; ring
  have e2 : (fun ω => armProb e a (X₁ ω) * (w (X₁ ω) / armProb e a (X₁ ω))) =ᵐ[μ₁]
      fun ω => w (X₁ ω) := by
    filter_upwards [hpos] with ω h
    field_simp
  have hw1 : Integrable (fun ω => w (X₁ ω)) μ₁ := by
    simpa using (integrable_densityRatio_mul_iff hX₁ hov (g := fun _ => (1 : ℝ))
      measurable_const).2 (integrable_const _)
  have hwint : ∫ ω, w (X₁ ω) ∂μ₁ = 1 := by
    simpa using (integral_densityRatio_mul hX₁ hov (g := fun _ => (1 : ℝ)) measurable_const).symm
  rw [e1]
  refine ⟨(integrable_respInd_arm_mul_iff hX₁ hA hps a hfm).2 (hw1.congr e2.symm), ?_⟩
  rw [integral_respInd_arm_mul_comp hX₁ hA hps a hfm, integral_congr_ae e2, hwint]

/-- **The self normalized transport identity.** Under the assumptions of the transport formula
`Transport.integral_target_eq_transport` for the arm `a` (indicator form of exchangeability,
propensity score `e` with `π_a(X₁) > 0` almost surely, a common regression `g`, overlap, and
integrability of `Y₂`, `Y₁(a)` and `w(X₁) Y₁(a)`), with a probability target, the self normalized
mean with the arm weights `w(X₁) 1{A = a} / π_a(X₁)` is the target mean:
`E[w 1{A = a} Y / π_a] / E[w 1{A = a} / π_a] = E₂[Y₂]`. -/
theorem hajek_transport_eq_targetMean [IsFiniteMeasure μ₁] [IsProbabilityMeasure μ₂]
    {Y₁ : Bool → Ω₁ → ℝ} {Y₂ : Ω₂ → ℝ} {g : 𝒳 → ℝ} (a : Bool) (hX₁ : Measurable X₁)
    (hX₂ : Measurable X₂) (hA : Measurable A) (hYa : Measurable (Y₁ a))
    (hY₁ : Integrable (Y₁ a) μ₁) (hY₂ : Integrable Y₂ μ₂) (hmar : MARMean μ₁ X₁ (Y₁ a) (arm A a))
    (hps : IsPropensityScore μ₁ A X₁ e) (hpos : ∀ᵐ ω ∂μ₁, 0 < armProb e a (X₁ ω))
    (hcom : IsCommonRegression μ₁ X₁ (Y₁ a) μ₂ X₂ Y₂ g) (hov : μ₂.map X₂ ≪ μ₁.map X₁)
    (hwY : Integrable (fun ω => densityRatio μ₁ X₁ μ₂ X₂ (X₁ ω) * Y₁ a ω) μ₁) :
    (∫ ω, densityRatio μ₁ X₁ μ₂ X₂ (X₁ ω) * respInd (arm A a) ω * obsOutcome A Y₁ ω /
        armProb e a (X₁ ω) ∂μ₁) /
      (∫ ω, densityRatio μ₁ X₁ μ₂ X₂ (X₁ ω) * ipwWeight A X₁ e a ω ∂μ₁) = ∫ ω, Y₂ ω ∂μ₂ := by
  rw [(integral_densityRatio_mul_ipwWeight hX₁ hA hps a hpos hov).2, div_one]
  exact (integral_target_eq_transport a hX₁ hX₂ hA hYa hY₁ hY₂ hmar hps hpos hcom hov
    hwY).2.2.2.2.symm

end Identities

/-! ### The population weighted arm mean -/

section TransportModel

variable {Ω₁ Ω₂ 𝒳 : Type*} [MeasurableSpace Ω₁] [MeasurableSpace Ω₂] [MeasurableSpace 𝒳]

/-- **The population weighted arm mean with inverse probability weights is the target mean.**
Let the arm `a` of a transport model be conditionally transportable and `e` be the propensity
score of the source study, with any dependence on the covariates. Then every measurable weight
function equal almost everywhere (under the source covariate law) to a nonzero multiple `C` of
`w / π_a`, with `w` the density ratio, gives
`E₁[w(X₁) 1{A = a} Y] / E₁[w(X₁) 1{A = a}] = E₂[Y₂(a)]`. The numerator is `C E₂[Y₂(a)]` by the
transport formula and the denominator is `C` (`integral_densityRatio_mul_ipwWeight`); positivity
of `π_a` is read off the positivity of the transportability assumption. -/
theorem lawWeightedArmMean_div_armProb_eq_targetMean {M : TransportModel Ω₁ Ω₂ 𝒳} {a : Bool}
    (hM : M.IsConditionallyTransportable a) {e : 𝒳 → ℝ}
    (hps : IsPropensityScore M.μ₁ M.A M.X₁ e) {C : ℝ} (hC : C ≠ 0) {w : 𝒳 → ℝ}
    (hwm : Measurable w)
    (hw : w =ᵐ[M.μ₁.map M.X₁] fun x => C * (densityRatio M.μ₁ M.X₁ M.μ₂ M.X₂ x / armProb e a x)) :
    lawWeightedArmMean M.sourceLaw w a = M.targetMean a := by
  have := hM.isProbabilityMeasure_μ₁
  have := hM.isProbabilityMeasure_μ₂
  have hX₁ := hM.measurable_X₁
  have hX₂ := hM.measurable_X₂
  have hA := hM.measurable_A
  obtain ⟨g, hcom⟩ := hM.structurallyInvariant
  set wd := densityRatio M.μ₁ M.X₁ M.μ₂ M.X₂ with hwd_def
  have hpos : ∀ᵐ ω ∂M.μ₁, 0 < armProb e a (M.X₁ ω) := by
    filter_upwards [hM.pos, hps.condExp_arm hX₁ hA a] with ω h1 h2
    rwa [h2] at h1
  obtain ⟨-, -, -, -, h5⟩ := integral_target_eq_transport a hX₁ hX₂ hA (hM.measurable_Y₁ a)
    hM.integrable_Y₁ hM.integrable_Y₂ hM.marMean hps hpos hcom hM.overlap hM.integrable_weight
  have hden1 := (integral_densityRatio_mul_ipwWeight hX₁ hA hps a hpos hM.overlap).2
  rw [← hwd_def] at h5 hden1
  have hsrc : Measurable fun ω => (M.X₁ ω, M.A ω, obsOutcome M.A M.Y₁ ω) :=
    hX₁.prodMk (hA.prodMk (measurable_obsOutcome hA hM.measurable_Y₁))
  have hite : Measurable fun z : 𝒳 × Bool × ℝ => if z.2.1 = a then w z.1 else 0 :=
    Measurable.ite ((measurable_fst.comp measurable_snd) (measurableSet_singleton a))
      (hwm.comp measurable_fst) measurable_const
  have hrw : ∀ ω, (if M.A ω = a then w (M.X₁ ω) else 0) = respInd (arm M.A a) ω * w (M.X₁ ω) :=
    fun ω => by rw [respInd_arm_apply]; split_ifs <;> simp
  have hae : ∀ᵐ ω ∂M.μ₁, w (M.X₁ ω) = C * (wd (M.X₁ ω) / armProb e a (M.X₁ ω)) :=
    ae_of_ae_map hX₁.aemeasurable hw
  have hnum : ∫ z, (if z.2.1 = a then w z.1 else 0) * z.2.2 ∂M.sourceLaw =
      C * M.targetMean a := by
    rw [TransportModel.sourceLaw, integral_map hsrc.aemeasurable
      (f := fun z : 𝒳 × Bool × ℝ => (if z.2.1 = a then w z.1 else 0) * z.2.2)
      (hite.mul (measurable_snd.comp measurable_snd)).aestronglyMeasurable,
      TransportModel.targetMean, h5, ← integral_const_mul]
    refine integral_congr_ae ?_
    filter_upwards [hae] with ω hω
    simp only [hrw]
    rw [hω]
    ring
  have hden : ∫ z, (if z.2.1 = a then w z.1 else 0) ∂M.sourceLaw = C := by
    rw [TransportModel.sourceLaw, integral_map hsrc.aemeasurable
      (f := fun z : 𝒳 × Bool × ℝ => if z.2.1 = a then w z.1 else 0) hite.aestronglyMeasurable]
    calc ∫ ω, (if M.A ω = a then w (M.X₁ ω) else 0) ∂M.μ₁
        = ∫ ω, C * (wd (M.X₁ ω) * ipwWeight M.A M.X₁ e a ω) ∂M.μ₁ := by
          refine integral_congr_ae ?_
          filter_upwards [hae] with ω hω
          simp only [hrw, ipwWeight]
          rw [hω]
          ring
      _ = C := by rw [integral_const_mul, hden1, mul_one]
  rw [lawWeightedArmMean, hnum, hden]
  field_simp

end TransportModel

/-! ### A design with covariate dependent assignment -/

section Design

/-- The assignment probability of the design: `P(A = true | x) = 3/4` at `x = true` and `1/4` at
`x = false`. -/
noncomputable def ipwDesignScore (x : Bool) : ℝ := if x then 3 / 4 else 1 / 4

/-- The masses of `(x, a)`: `x` equally likely and `a` assigned with probability
`ipwDesignScore x`, so `1/8, 3/8, 3/8, 1/8` at `(false, true)`, `(false, false)`, `(true, true)`,
`(true, false)`. -/
noncomputable def ipwDesignMass (ω : Bool × Bool) : ℝ :=
  1 / 2 * armProb ipwDesignScore ω.2 ω.1

theorem isWeights_ipwDesignMass : IsWeights ipwDesignMass := by
  refine ⟨fun ω => ?_, ?_⟩
  · rcases ω with ⟨_ | _, _ | _⟩ <;> norm_num [ipwDesignMass, armProb, ipwDesignScore]
  · simp only [Fintype.sum_prod_type, Fintype.sum_bool, ipwDesignMass, armProb, ipwDesignScore]
    norm_num

/-- The law of `(x, a)` in the design. -/
noncomputable def ipwDesignLaw : Measure (Bool × Bool) := stratumLaw ipwDesignMass

instance : IsProbabilityMeasure ipwDesignLaw :=
  isProbabilityMeasure_stratumLaw isWeights_ipwDesignMass

theorem integral_ipwDesignLaw (f : Bool × Bool → ℝ) :
    ∫ ω, f ω ∂ipwDesignLaw = (f (false, true) + 3 * f (false, false) + 3 * f (true, true) +
      f (true, false)) / 8 := by
  rw [ipwDesignLaw, integral_stratumLaw isWeights_ipwDesignMass.1, standardizedRisk]
  simp only [Fintype.sum_prod_type, Fintype.sum_bool, ipwDesignMass, armProb, ipwDesignScore]
  norm_num
  ring

/-- The outcome `Y(t) = 1{x}` of the design, for both arms. -/
noncomputable def ipwDesignOutcome (x : Bool) : ℝ := if x then 1 else 0

/-- The transport model of the design: the source is `ipwDesignLaw` with covariate `x`,
treatment `a` and outcomes `Y(t) = 1{x}`; the target is the source itself. -/
noncomputable def ipwDesignModel : TransportModel (Bool × Bool) (Bool × Bool) Bool where
  μ₁ := ipwDesignLaw
  X₁ := Prod.fst
  A := Prod.snd
  Y₁ _ ω := ipwDesignOutcome ω.1
  μ₂ := ipwDesignLaw
  X₂ := Prod.fst
  Y₂ _ ω := ipwDesignOutcome ω.1

/-- **The propensity score of the design** is `ipwDesignScore`. -/
theorem isPropensityScore_ipwDesign :
    IsPropensityScore ipwDesignLaw Prod.snd Prod.fst ipwDesignScore := by
  refine ⟨Measurable.of_discrete, (ae_eq_condExp_of_forall_setIntegral_eq measurable_fst.comap_le
    Integrable.of_finite (fun _ _ _ => Integrable.of_finite.integrableOn) ?_
    ((Measurable.of_discrete (f := ipwDesignScore)).comp
      (comap_measurable Prod.fst)).aestronglyMeasurable).symm⟩
  rintro s ⟨B, -, rfl⟩ -
  have hs : MeasurableSet ((Prod.fst : Bool × Bool → Bool) ⁻¹' B) :=
    measurable_fst (Set.Finite.measurableSet (Set.toFinite B))
  rw [← integral_indicator hs, ← integral_indicator hs, integral_ipwDesignLaw,
    integral_ipwDesignLaw]
  simp only [Set.indicator, Set.mem_preimage, respInd_apply]
  by_cases h0 : false ∈ B <;> by_cases h1 : true ∈ B <;> simp [h0, h1] <;>
    norm_num [ipwDesignScore]

theorem comap_fst_outcome_eq :
    MeasurableSpace.comap (fun ω : Bool × Bool => (ω.1, ipwDesignOutcome ω.1)) inferInstance =
      MeasurableSpace.comap Prod.fst inferInstance := by
  refine le_antisymm ?_ ?_
  · exact Measurable.comap_le ((Measurable.of_discrete (f := fun x : Bool =>
      (x, ipwDesignOutcome x))).comp (comap_measurable Prod.fst))
  · rintro s ⟨t, ht, rfl⟩
    exact ⟨Prod.fst ⁻¹' t, measurable_fst ht, rfl⟩

/-- **The arm `true` of the design is conditionally transportable**: exchangeability holds
because the outcome is a function of the covariate, positivity because the assignment
probability is at least `1/4`, and the target is the source. -/
theorem isConditionallyTransportable_ipwDesign :
    ipwDesignModel.IsConditionallyTransportable true := by
  have hcr : IsCommonRegression ipwDesignLaw Prod.fst (fun ω => ipwDesignOutcome ω.1)
      ipwDesignLaw Prod.fst (fun ω => ipwDesignOutcome ω.1) ipwDesignOutcome := by
    have hsm : StronglyMeasurable[MeasurableSpace.comap Prod.fst inferInstance]
        fun ω : Bool × Bool => ipwDesignOutcome ω.1 :=
      ((Measurable.of_discrete (f := ipwDesignOutcome)).comp
        (comap_measurable (Prod.fst : Bool × Bool → Bool))).stronglyMeasurable
    have h := condExp_of_stronglyMeasurable (μ := ipwDesignLaw) measurable_fst.comap_le hsm
      Integrable.of_finite
    exact ⟨Measurable.of_discrete, by rw [h], by rw [h]⟩
  have : IsProbabilityMeasure ipwDesignModel.μ₁ :=
    inferInstanceAs (IsProbabilityMeasure ipwDesignLaw)
  have : IsProbabilityMeasure ipwDesignModel.μ₂ :=
    inferInstanceAs (IsProbabilityMeasure ipwDesignLaw)
  refine ⟨inferInstanceAs (IsProbabilityMeasure ipwDesignLaw),
    inferInstanceAs (IsProbabilityMeasure ipwDesignLaw), measurable_fst, measurable_snd,
    fun _ => (Measurable.of_discrete (f := ipwDesignOutcome)).comp measurable_fst, measurable_fst,
    Integrable.of_finite, Integrable.of_finite, ?_, ?_, ⟨_, hcr⟩,
    Measure.AbsolutelyContinuous.rfl, Integrable.of_finite⟩
  · change ipwDesignLaw[respInd (arm Prod.snd true) | MeasurableSpace.comap
      (fun ω : Bool × Bool => (ω.1, ipwDesignOutcome ω.1)) inferInstance] =ᵐ[ipwDesignLaw]
      ipwDesignLaw[respInd (arm Prod.snd true) | MeasurableSpace.comap Prod.fst inferInstance]
    rw [comap_fst_outcome_eq]
  · filter_upwards [isPropensityScore_ipwDesign.condExp_arm measurable_fst measurable_snd true]
      with ω hω
    change 0 < ipwDesignLaw[respInd (arm Prod.snd true) |
      MeasurableSpace.comap Prod.fst inferInstance] ω
    rw [hω]
    cases ω.1 <;> norm_num [armProb, ipwDesignScore]

theorem integral_sourceLaw_ipwDesign {f : Bool × Bool × ℝ → ℝ} (hf : Measurable f) :
    ∫ z, f z ∂ipwDesignModel.sourceLaw = (f (false, true, 0) + 3 * f (false, false, 0) +
      3 * f (true, true, 1) + f (true, false, 1)) / 8 := by
  rw [TransportModel.sourceLaw, integral_map (Measurable.of_discrete).aemeasurable
    hf.aestronglyMeasurable]
  change ∫ ω, f (ω.1, ω.2, ipwDesignOutcome ω.1) ∂ipwDesignLaw = _
  rw [integral_ipwDesignLaw]
  norm_num [ipwDesignOutcome]

/-- **The weighted arm mean of the treated arm of the design** with any weights `w` is
`3 w(true) / (w(false) + 3 w(true))`. -/
theorem lawWeightedArmMean_ipwDesign (w : Bool → ℝ) :
    lawWeightedArmMean ipwDesignModel.sourceLaw w true = 3 * w true / (w false + 3 * w true) := by
  have hm : Measurable fun z : Bool × Bool × ℝ => if z.2.1 = true then w z.1 else 0 :=
    Measurable.ite ((measurable_fst.comp measurable_snd) (measurableSet_singleton true))
      ((Measurable.of_discrete (f := w)).comp measurable_fst) measurable_const
  rw [lawWeightedArmMean, integral_sourceLaw_ipwDesign (f := fun z : Bool × Bool × ℝ =>
    (if z.2.1 = true then w z.1 else 0) * z.2.2) (hm.mul (measurable_snd.comp measurable_snd)),
    integral_sourceLaw_ipwDesign hm]
  simp only [ite_true, Bool.false_eq_true, ite_false]
  rw [div_div_div_cancel_right₀ (by norm_num : (8 : ℝ) ≠ 0)]
  ring

/-- **The density ratio of the design is one** almost everywhere, since the target is the
source. -/
theorem densityRatio_ipwDesign_ae_eq_one :
    densityRatio ipwDesignModel.μ₁ ipwDesignModel.X₁ ipwDesignModel.μ₂ ipwDesignModel.X₂
      =ᵐ[ipwDesignModel.μ₁.map ipwDesignModel.X₁] fun _ => 1 := by
  change (fun x => ((ipwDesignLaw.map Prod.fst).rnDeriv (ipwDesignLaw.map Prod.fst) x).toReal)
    =ᵐ[ipwDesignLaw.map Prod.fst] fun _ => 1
  filter_upwards [Measure.rnDeriv_self (ipwDesignLaw.map Prod.fst)] with x hx
  rw [hx]
  rfl

/-- **Inverse probability weights are needed when assignment depends on the covariates.** In
the design (`x` equally likely, `P(A = true | x)` equal to `3/4` at `x = true` and `1/4` at
`x = false`, outcome `1{x}`, target equal to source):

* the arm `true` is conditionally transportable and the target mean is `1/2`;
* the weights `1 / π_true(x)`, equal almost everywhere to `w / π_true` with `w` the density
  ratio, give the weighted arm mean `1/2`, as `lawWeightedArmMean_div_armProb_eq_targetMean`
  states;
* the density ratio alone (equal to one) gives `3/4`. -/
theorem ipwDesign_results :
    ipwDesignModel.targetMean true = 1 / 2 ∧
      lawWeightedArmMean ipwDesignModel.sourceLaw (fun x => 1 / armProb ipwDesignScore true x)
        true = 1 / 2 ∧
      lawWeightedArmMean ipwDesignModel.sourceLaw (fun _ => 1) true = 3 / 4 := by
  have ht : ipwDesignModel.targetMean true = 1 / 2 := by
    change ∫ ω, ipwDesignOutcome ω.1 ∂ipwDesignLaw = 1 / 2
    rw [integral_ipwDesignLaw]
    norm_num [ipwDesignOutcome]
  refine ⟨ht, ?_, ?_⟩
  · rw [lawWeightedArmMean_div_armProb_eq_targetMean isConditionallyTransportable_ipwDesign
      isPropensityScore_ipwDesign one_ne_zero Measurable.of_discrete, ht]
    filter_upwards [densityRatio_ipwDesign_ae_eq_one] with x hx
    rw [hx, one_mul]
  · rw [lawWeightedArmMean_ipwDesign]
    norm_num

end Design

end PopulationAdjustment

end CausalInference
