/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.PopulationAdjustment.StandardizationInstancesLogisticLaw

/-!
# The logistic outcome model makes the potential outcomes integrable

The large sample theorems of standardization with a logistic fit assume integrable potential
outcomes `Y(t)` in the trial. In a randomized trial this premise follows from the logistic
outcome model itself, so it can be dropped.

* `Trial.LogisticOutcomeModel.ae_obsOutcome_mem`: the records follow the logistic family, whose
  base measure on the outcome is carried by `{0, 1}`; hence the observed outcome is `0` or `1`
  almost surely.
* `Trial.LogisticOutcomeModel.ae_potentialOutcome_mem`: in a randomized trial the assignment is
  independent of `Y(t)` and `P(A = t) > 0`, and `Y = Y(t)` on `{A = t}`; hence `Y(t)` is `0` or
  `1` almost surely.
* `Trial.LogisticOutcomeModel.integrable_potentialOutcome`: hence `Y(t)` is integrable.

The theorems `tendstoInMeasure_logisticModel_linkMarginal`, `_unanchored`, `_anchored`,
`_sampleMean_armMean` and `_conditionalPlugIn` are the consistency results of the standardized
logistic fit with the integrability premise on the potential outcomes removed.

## Main results

* `Trial.LogisticOutcomeModel.ae_obsOutcome_mem`,
  `Trial.LogisticOutcomeModel.ae_potentialOutcome_mem`,
  `Trial.LogisticOutcomeModel.integrable_potentialOutcome`.
* `tendstoInMeasure_logisticModel_linkMarginal`, `tendstoInMeasure_logisticModel_unanchored`,
  `tendstoInMeasure_logisticModel_anchored`, `tendstoInMeasure_logisticModel_sampleMean_armMean`,
  `tendstoInMeasure_logisticModel_conditionalPlugIn`.
-/

@[expose] public section

namespace CausalInference

namespace PopulationAdjustment

open MeasureTheory ProbabilityTheory Filter Topology Matrix EffectMeasure IndirectComparison
  PointTreatment Transport

variable {Ω₁ Ω₂ Ξ 𝒳 ι κ : Type*} [MeasurableSpace Ω₁] [MeasurableSpace Ω₂] [MeasurableSpace Ξ]
  [MeasurableSpace 𝒳] [Fintype κ] {T : Trial Ω₁ 𝒳 Bool} [IsProbabilityMeasure T.μ]
  {z : 𝒳 × Bool → κ → ℝ} {ξ₀ : κ → ℝ}

/-- The set of real numbers other than `0` and `1`. -/
theorem measurableSet_not_zero_or_one : MeasurableSet {y : ℝ | ¬ (y = 0 ∨ y = 1)} :=
  ((measurableSet_singleton (0 : ℝ)).union (measurableSet_singleton 1)).compl

/-- **Under the logistic outcome model the observed outcome is binary.** The law of the records
has a density with respect to `R ⊗ (δ₀ + δ₁)`, which gives no mass to outcomes other than `0`
and `1`. -/
theorem _root_.CausalInference.IndirectComparison.Trial.LogisticOutcomeModel.ae_obsOutcome_mem
    (hT : T.IsRandomizedTwoArm) (hM : T.LogisticOutcomeModel z ξ₀) :
    ∀ᵐ ω ∂T.μ, T.obsOutcome ω = 0 ∨ T.obsOutcome ω = 1 := by
  set S : Set ((𝒳 × Bool) × ℝ) := Set.univ ×ˢ {y : ℝ | ¬ (y = 0 ∨ y = 1)}
  have hS : MeasurableSet S := MeasurableSet.univ.prod measurableSet_not_zero_or_one
  have hlam : (Measure.dirac (0 : ℝ) + Measure.dirac (1 : ℝ) : Measure ℝ)
      {y : ℝ | ¬ (y = 0 ∨ y = 1)} = 0 := by
    rw [add_apply, Measure.dirac_apply' _ measurableSet_not_zero_or_one,
      Measure.dirac_apply' _ measurableSet_not_zero_or_one]
    simp
  have hν : ((T.μ.map fun ω => (T.X ω, T.A ω)).prod logisticKernel.lam) S = 0 := by
    rw [Measure.prod_prod]
    change _ * (Measure.dirac (0 : ℝ) + Measure.dirac (1 : ℝ) : Measure ℝ)
      {y : ℝ | ¬ (y = 0 ∨ y = 1)} = 0
    rw [hlam, mul_zero]
  have hlaw : (glmFamily logisticKernel (T.μ.map fun ω => (T.X ω, T.A ω)) z
      hM.measurable_z).law ξ₀ S = 0 :=
    withDensity_absolutelyContinuous _ _ hν
  have hrec : Measurable fun ω => ((T.X ω, T.A ω), T.obsOutcome ω) :=
    (hT.measurable_X.prodMk hT.measurable_A).prodMk
      (measurable_obsOutcome hT.measurable_A hT.measurable_Y)
  rw [← hM.law_eq, Measure.map_apply hrec hS] at hlaw
  rw [ae_iff]
  refine measure_mono_null (fun ω hω => ?_) hlaw
  exact ⟨Set.mem_univ _, hω⟩

/-- **Under the logistic outcome model in a randomized trial the potential outcomes are
binary.** On `{A = t}` the observed outcome is `Y(t)`, the assignment is independent of `Y(t)`
and `P(A = t) > 0`, so `P(Y(t) ∉ {0, 1}) = 0`. -/
theorem _root_.CausalInference.IndirectComparison.Trial.LogisticOutcomeModel.ae_potentialOutcome_mem
    (hT : T.IsRandomizedTwoArm) (hM : T.LogisticOutcomeModel z ξ₀) (t : Bool) :
    ∀ᵐ ω ∂T.μ, T.Y t ω = 0 ∨ T.Y t ω = 1 := by
  set B : Set ℝ := {y : ℝ | ¬ (y = 0 ∨ y = 1)}
  have hind : IndepFun T.A (T.Y t) T.μ := by
    cases t
    · exact hT.indepFun.comp measurable_id (measurable_fst.comp measurable_snd)
    · exact hT.indepFun.comp measurable_id (measurable_snd.comp measurable_snd)
  have hA : 0 < T.μ.real (T.A ⁻¹' {t}) := by
    cases t
    · have hs : MeasurableSet (T.A ⁻¹' {true}) := hT.measurable_A (measurableSet_singleton _)
      have e : T.A ⁻¹' {false} = (T.A ⁻¹' {true})ᶜ := by ext ω; simp
      have h := probReal_add_probReal_compl (μ := T.μ) hs
      rw [e]
      linarith [hT.prob_lt_one]
    · exact hT.prob_pos
  have hA' : T.μ (T.A ⁻¹' {t}) ≠ 0 := by
    intro h
    rw [measureReal_def, h, ENNReal.toReal_zero] at hA
    exact lt_irrefl _ hA
  have hobs := hM.ae_obsOutcome_mem hT
  rw [ae_iff] at hobs
  have hinter : T.μ (T.A ⁻¹' {t} ∩ T.Y t ⁻¹' B) = 0 := by
    refine measure_mono_null (fun ω hω => ?_) hobs
    obtain ⟨h1, h2⟩ := hω
    simp only [Set.mem_preimage, Set.mem_singleton_iff] at h1
    simp only [Set.mem_ofPred_eq, Trial.obsOutcome, h1]
    exact h2
  rw [indepFun_iff_measure_inter_preimage_eq_mul] at hind
  rw [hind _ _ (measurableSet_singleton t) measurableSet_not_zero_or_one, mul_eq_zero] at hinter
  rw [ae_iff]
  exact hinter.resolve_left hA'

/-- **Under the logistic outcome model in a randomized trial the potential outcomes are
integrable.** -/
theorem
    _root_.CausalInference.IndirectComparison.Trial.LogisticOutcomeModel.integrable_potentialOutcome
    (hT : T.IsRandomizedTwoArm) (hM : T.LogisticOutcomeModel z ξ₀) (t : Bool) :
    Integrable (T.Y t) T.μ :=
  integrable_of_ae_zero_or_one (hT.measurable_Y t) (hM.ae_potentialOutcome_mem hT t)

/-! ### The consistency theorems without the integrability premise -/

variable {Q : Population Ω₂ 𝒳 ι} {P : Measure Ξ} {K : Set (κ → ℝ)}
  {O : ℕ → Ξ → (𝒳 × Bool) × ℝ}

/-- **The standardized logistic marginal effect is consistent**, with integrability of the
potential outcomes proved from the logistic outcome model
(`tendstoInMeasure_logistic_linkMarginal` without that premise). -/
theorem tendstoInMeasure_logisticModel_linkMarginal [IsProbabilityMeasure Q.μ]
    [IsProbabilityMeasure P] (hT : T.IsRandomizedTwoArm) (hM : T.LogisticOutcomeModel z ξ₀)
    (hK : IsCompact K) (hξ₀ : ξ₀ ∈ K) (hO : IsIIDSample O P)
    (hlaw : P.map (O 0) = T.μ.map fun ω => ((T.X ω, T.A ω), T.obsOutcome ω))
    (hX₂ : Measurable Q.X) {t₀ t₁ : Bool} {s₀ s₁ : ι} (hYQ₀ : Integrable (Q.Y s₀) Q.μ)
    (hYQ₁ : Integrable (Q.Y s₁) Q.μ)
    (hsi₀ : StructurallyInvariant T.μ T.X (T.Y t₀) Q.μ Q.X (Q.Y s₀))
    (hsi₁ : StructurallyInvariant T.μ T.X (T.Y t₁) Q.μ Q.X (Q.Y s₁)) (hov : Q.covLaw ≪ T.covLaw)
    {g : ℝ → ℝ} (hg₀ : ContinuousAt g (Q.armMean s₀)) (hg₁ : ContinuousAt g (Q.armMean s₁)) :
    TendstoInMeasure P
      (fun n ω => linkMarginal g Q.covLaw
        (fun x => Real.sigmoid (z (x, t₀) ⬝ᵥ glmMLE logisticDens z K O n ω))
        (fun x => Real.sigmoid (z (x, t₁) ⬝ᵥ glmMLE logisticDens z K O n ω)))
      atTop (fun _ => Q.marginalEffect g s₀ s₁) :=
  tendstoInMeasure_logistic_linkMarginal hT (hM.integrable_potentialOutcome hT) hM hK hξ₀ hO hlaw
    hX₂ hYQ₀ hYQ₁ hsi₀ hsi₁ hov hg₀ hg₁

/-- **The unanchored comparison with the standardized logistic fit is consistent**, with
integrability of the potential outcomes proved from the logistic outcome model. The arm `t` of
the trial stands for `a`; a reported target mean `m̂_b` converges in probability to
`E_Q[Y(b)]`. -/
theorem tendstoInMeasure_logisticModel_unanchored [IsProbabilityMeasure Q.μ]
    [IsProbabilityMeasure P] (hT : T.IsRandomizedTwoArm) (hM : T.LogisticOutcomeModel z ξ₀)
    (hK : IsCompact K) (hξ₀ : ξ₀ ∈ K) (hO : IsIIDSample O P)
    (hlaw : P.map (O 0) = T.μ.map fun ω => ((T.X ω, T.A ω), T.obsOutcome ω))
    (hX₂ : Measurable Q.X) {t : Bool} {a b : ι} (hYQ : Integrable (Q.Y a) Q.μ)
    (hsi : StructurallyInvariant T.μ T.X (T.Y t) Q.μ Q.X (Q.Y a)) (hov : Q.covLaw ≪ T.covLaw)
    {mb : ℕ → Ξ → ℝ} (hmb : TendstoInMeasure P mb atTop fun _ => Q.armMean b) {g : ℝ → ℝ}
    (hga : ContinuousAt g (Q.armMean a)) (hgb : ContinuousAt g (Q.armMean b)) :
    TendstoInMeasure P
      (fun n ω => g (mb n ω) -
        g (∫ x, Real.sigmoid (z (x, t) ⬝ᵥ glmMLE logisticDens z K O n ω) ∂Q.covLaw))
      atTop (fun _ => Q.marginalEffect g a b) := by
  have : IsProbabilityMeasure Q.covLaw := by unfold Population.covLaw; infer_instance
  have hYi := hM.integrable_potentialOutcome hT
  have hr := logisticSurface_regular hM.measurable_z t Q.covLaw
  exact tendstoInMeasure_unanchored_fit (h := fun ξ t x => Real.sigmoid (z (x, t) ⬝ᵥ ξ)) hT
    hYi (hM.isOutcomeRegression hT hYi) hX₂ hYQ hsi hov
    (Eventually.of_forall fun ξ => (hr.1 ξ).aestronglyMeasurable) hr.2.1
    (Eventually.of_forall fun ξ => ae_of_all _ (hr.2.2.1 ξ))
    (ae_of_all _ fun x => (hr.2.2.2 x).continuousAt) (hM.tendstoInMeasure hT hK hξ₀ hO hlaw)
    hmb hga hgb

/-- **The anchored comparison with the standardized logistic fit is consistent**, with
integrability of the potential outcomes proved from the logistic outcome model
(`tendstoInMeasure_logistic_anchored` without that premise). -/
theorem tendstoInMeasure_logisticModel_anchored [IsProbabilityMeasure Q.μ]
    [IsProbabilityMeasure P] (hT : T.IsRandomizedTwoArm) (hM : T.LogisticOutcomeModel z ξ₀)
    (hK : IsCompact K) (hξ₀ : ξ₀ ∈ K) (hO : IsIIDSample O P)
    (hlaw : P.map (O 0) = T.μ.map fun ω => ((T.X ω, T.A ω), T.obsOutcome ω))
    (hX₂ : Measurable Q.X) {ta tc : Bool} {a b c : ι} (hYQa : Integrable (Q.Y a) Q.μ)
    (hYQc : Integrable (Q.Y c) Q.μ)
    (hsia : StructurallyInvariant T.μ T.X (T.Y ta) Q.μ Q.X (Q.Y a))
    (hsic : StructurallyInvariant T.μ T.X (T.Y tc) Q.μ Q.X (Q.Y c)) (hov : Q.covLaw ≪ T.covLaw)
    {dbc : ℕ → Ξ → ℝ} {g : ℝ → ℝ}
    (hdbc : TendstoInMeasure P dbc atTop fun _ => Q.marginalEffect g b c)
    (hga : ContinuousAt g (Q.armMean a)) (hgc : ContinuousAt g (Q.armMean c)) :
    TendstoInMeasure P
      (fun n ω => linkMarginal g Q.covLaw
        (fun x => Real.sigmoid (z (x, ta) ⬝ᵥ glmMLE logisticDens z K O n ω))
        (fun x => Real.sigmoid (z (x, tc) ⬝ᵥ glmMLE logisticDens z K O n ω)) - dbc n ω)
      atTop (fun _ => Q.marginalEffect g a b) :=
  tendstoInMeasure_logistic_anchored hT (hM.integrable_potentialOutcome hT) hM hK hξ₀ hO hlaw
    hX₂ hYQa hYQc hsia hsic hov hdbc hga hgc

/-- **The average of the logistic fit over target draws is consistent for the target arm
mean**, with integrability of the potential outcomes proved from the logistic outcome model
(`tendstoInMeasure_logistic_sampleMean_armMean` without that premise). -/
theorem tendstoInMeasure_logisticModel_sampleMean_armMean [IsProbabilityMeasure Q.μ]
    [IsProbabilityMeasure P] (hT : T.IsRandomizedTwoArm) (hM : T.LogisticOutcomeModel z ξ₀)
    (hK : IsCompact K) (hξ₀ : ξ₀ ∈ K) (hO : IsIIDSample O P)
    (hlaw : P.map (O 0) = T.μ.map fun ω => ((T.X ω, T.A ω), T.obsOutcome ω))
    (hX₂ : Measurable Q.X) {t : Bool} {s : ι} (hYQ : Integrable (Q.Y s) Q.μ)
    (hsi : StructurallyInvariant T.μ T.X (T.Y t) Q.μ Q.X (Q.Y s)) (hov : Q.covLaw ≪ T.covLaw)
    {Xs : ℕ → Ξ → 𝒳} (hXs : IsIIDSample Xs P) (hν : P.map (Xs 0) = Q.covLaw) {m : ℕ → ℕ}
    (hm : Tendsto m atTop atTop) :
    TendstoInMeasure P
      (fun n ω => sampleMean (fun x => Real.sigmoid (z (x, t) ⬝ᵥ glmMLE logisticDens z K O n ω))
        Xs (m n) ω) atTop (fun _ => Q.armMean s) :=
  tendstoInMeasure_logistic_sampleMean_armMean hT (hM.integrable_potentialOutcome hT) hM hK hξ₀
    hO hlaw hX₂ hYQ hsi hov hXs hν hm

/-- **The conditional plug-in of the logistic fit converges to the marginal log odds ratio plus
the difference of the averaging gaps**, with integrability of the potential outcomes proved
from the logistic outcome model (`tendstoInMeasure_logistic_conditionalPlugIn` without that
premise). -/
theorem tendstoInMeasure_logisticModel_conditionalPlugIn {p : ℕ}
    {T : Trial Ω₁ (Fin p → ℝ) Bool} {Q : Population Ω₂ (Fin p → ℝ) ι}
    {ξ₀ : Option (Fin p) ⊕ Option (Fin p) → ℝ} {K : Set (Option (Fin p) ⊕ Option (Fin p) → ℝ)}
    {O : ℕ → Ξ → ((Fin p → ℝ) × Bool) × ℝ} [IsProbabilityMeasure T.μ]
    [IsProbabilityMeasure Q.μ] [IsProbabilityMeasure P] (hT : T.IsRandomizedTwoArm)
    (hM : T.LogisticOutcomeModel (fun c => interactionDesign c.2 c.1) ξ₀) (hK : IsCompact K)
    (hξ₀ : ξ₀ ∈ K) (hO : IsIIDSample O P)
    (hlaw : P.map (O 0) = T.μ.map fun ω => ((T.X ω, T.A ω), T.obsOutcome ω))
    (hX₂ : Measurable Q.X) {s₀ s₁ : ι} (hYQ₀ : Integrable (Q.Y s₀) Q.μ)
    (hYQ₁ : Integrable (Q.Y s₁) Q.μ)
    (hsi₀ : StructurallyInvariant T.μ T.X (T.Y false) Q.μ Q.X (Q.Y s₀))
    (hsi₁ : StructurallyInvariant T.μ T.X (T.Y true) Q.μ Q.X (Q.Y s₁))
    (hov : Q.covLaw ≪ T.covLaw) (hν : ∀ k, Integrable (fun x : Fin p → ℝ => x k) Q.covLaw)
    {xh : ℕ → Ξ → Fin p → ℝ} (hx : TendstoInMeasure P xh atTop fun _ => covMean Q.covLaw) :
    TendstoInMeasure P
      (fun n ω => linkContrast logit
        (fun x => Real.sigmoid (interactionDesign false x ⬝ᵥ
          glmMLE logisticDens (fun c => interactionDesign c.2 c.1) K O n ω))
        (fun x => Real.sigmoid (interactionDesign true x ⬝ᵥ
          glmMLE logisticDens (fun c => interactionDesign c.2 c.1) K O n ω)) (xh n ω)) atTop
      (fun _ => Q.marginalEffect logit s₀ s₁ +
        (averagingGap logit Q.covLaw (fun x => Real.sigmoid (interactionDesign false x ⬝ᵥ ξ₀)) -
          averagingGap logit Q.covLaw (fun x => Real.sigmoid (interactionDesign true x ⬝ᵥ ξ₀)))) :=
  tendstoInMeasure_logistic_conditionalPlugIn hT (hM.integrable_potentialOutcome hT) hM hK hξ₀
    hO hlaw hX₂ hYQ₀ hYQ₁ hsi₀ hsi₁ hov hν hx

end PopulationAdjustment

end CausalInference
