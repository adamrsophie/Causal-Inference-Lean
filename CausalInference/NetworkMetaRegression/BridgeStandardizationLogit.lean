/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.NetworkMetaRegression.BridgeStandardization
public import CausalInference.PopulationAdjustment.CommonLimitLikelihood
public import CausalInference.PopulationAdjustment.CommonLimitFollowUpGeneral
public import CausalInference.PopulationAdjustment.OutcomeModelExamples

/-!
# The multilevel model with the logit link: the limits of weighting and standardization

A randomized trial of `a` (arm `true`) against `c` (arm `false`) has a binary outcome whose law
given the covariates `x` and the arm is the logistic model of the multilevel network
meta-regression at the trial baseline `μ_T`: `P(Y = 1 | x, k) = σ(η_k(φ(x)))` with
`η_k(u) = μ_T + γ_k + uᵀ(β₁ + β₂,k)`. In the interaction design of the features this is the
logistic family `glmFamily logisticKernel` at the coefficients `ipdCoef M μ_T a c`.

* **The model** (`Trial.logisticOutcomeModel_featureInteraction`): for bounded measurable
  features with the margin condition at `t`, the law of the records alone gives the logistic
  outcome model of the library: the design is measurable, integrable and of full rank. The
  regression of the trial is the multilevel surface (`isOutcomeRegression_surface_sigmoid`).
* **The limits** (`MultilevelModel.commonLimit_logit`): for an i.i.d. sample of the records,
  * the logistic maximum likelihood fit converges in probability to `ipdCoef M μ_T a c`;
  * the standardized marginal log odds ratio over a target covariate law `Q_X` converges in
    probability to the marginal log odds ratio of the multilevel surfaces under `Q_X`,
    `linkMarginal logit (Q_X ∘ φ⁻¹) (σ ∘ η_c) (σ ∘ η_a)`;
  * the weighted log odds ratio (entropy balancing at the feature means `t`) converges in
    probability to the same functional under another law: the trial covariate law tilted by the
    population entropy balancing weights, which has the feature means `t` but is in general not
    the target law.
* **When the two limits agree** (`MultilevelModel.commonLimit_logit_of_affine`): if the
  multilevel risk of each arm is affine in the features, `σ(η_k(φ(x))) = α_k + β_kᵀφ(x)`, and
  `t` is the target feature mean, both limits are `logit(α_a + β_aᵀt) - logit(α_c + β_cᵀt)` and
  the difference of the two estimators converges in probability to `0`. This holds for every
  model when the features take two values (a binary covariate); with three feature values and a
  nonzero slope it fails in general (`BridgeStandardizationLogitExamples`).
* **The target effect** (`MultilevelModel.commonLimit_logit_marginalEffect`): if
  the conditional risks of `Y(a)` and `Y(c)` in the target are the multilevel surfaces at the
  baseline `μ_T`, the standardized limit is the target marginal log odds ratio. On the logit
  scale the baseline does not cancel: at another target baseline the marginal log odds ratio is
  another number (`logitTriangle_marginal_shift`).

## Main results

* `featureInteractionDesign_eq_zero_of_ae`, `Trial.logisticOutcomeModel_featureInteraction`.
* `integral_sigmoid_mem_Ioo`, `isProbabilityMeasure_entropyTiltedLaw`.
* `MultilevelModel.isOutcomeRegression_surface_sigmoid`, `MultilevelModel.commonLimit_logit`,
  `MultilevelModel.commonLimit_logit_of_affine`, `MultilevelModel.commonLimit_logit_marginalEffect`.

## References

* D. M. Phillippo, S. Dias, A. E. Ades, M. Belger, A. Brnabic, A. Schacht, D. Saure, Z. Kadziola
  and N. J. Welton, *Multilevel network meta-regression for population-adjusted treatment
  comparisons*, Journal of the Royal Statistical Society Series A 183 (2020).
* J. E. Signorovitch and coauthors, PharmacoEconomics 28 (2010).
-/

@[expose] public section

namespace CausalInference

namespace NetworkMetaRegression

open MeasureTheory ProbabilityTheory Filter Topology Matrix EffectMeasure IndirectComparison
  PointTreatment Transport PopulationAdjustment

variable {Ω₁ Ω₂ Ξ 𝒳 ι : Type*} [MeasurableSpace Ω₁] [MeasurableSpace Ω₂] [MeasurableSpace Ξ]
  [MeasurableSpace 𝒳] {p : ℕ} {T : Trial Ω₁ 𝒳 Bool} {φ : 𝒳 → Fin p → ℝ} {t : Fin p → ℝ}

/-! ### The logistic outcome model from the law of the records -/

/-- The coordinates of the interaction design are measurable functions of the pair
`(x, arm)`. -/
theorem measurable_featureInteractionDesign_pair (hφ : Measurable φ)
    (j : Option (Fin p) ⊕ Option (Fin p)) :
    Measurable fun q : 𝒳 × Bool => featureInteractionDesign φ q.2 q.1 j :=
  measurable_from_prod_countable_left fun a => measurable_featureInteractionDesign hφ a j

/-- **The interaction design has full rank in a randomized trial with the margin condition**: if
`z(A, X)ᵀv = 0` almost surely, randomization gives `z(a, X)ᵀv = 0` almost surely in each arm, and
the margin condition at `t` forces each of the two affine functions of the features to vanish, so
`v = 0`. -/
theorem featureInteractionDesign_eq_zero_of_ae [IsProbabilityMeasure T.μ]
    (hT : T.IsRandomizedTwoArm) (hφ : Measurable φ) {δ : ℝ} (hδ : 0 < δ)
    (hmargin : ∀ v : Fin p → ℝ, ‖v‖ = 1 → δ ≤ T.covLaw.real {x | δ ≤ v ⬝ᵥ (φ x - t)})
    {v : Option (Fin p) ⊕ Option (Fin p) → ℝ}
    (hv : ∀ᵐ ω ∂T.μ, featureInteractionDesign φ (T.A ω) (T.X ω) ⬝ᵥ v = 0) : v = 0 := by
  have : IsProbabilityMeasure T.covLaw := T.isProbabilityMeasure_covLaw hT.measurable_X
  have hsm : ∀ a, Measurable fun x => featureInteractionDesign φ a x ⬝ᵥ v := fun a =>
    Finset.measurable_sum _ fun k _ => (measurable_featureInteractionDesign hφ a k).mul_const _
  have harm : ∀ a : Bool, ∀ᵐ x ∂T.covLaw, featureInteractionDesign φ a x ⬝ᵥ v = 0 := by
    intro a
    have hS : MeasurableSet {x | ¬ featureInteractionDesign φ a x ⬝ᵥ v = 0} :=
      (measurableSet_eq_fun (hsm a) measurable_const).compl
    rw [ae_iff, Population.covLaw, Measure.map_apply hT.measurable_X hS]
    have h0 : T.μ (T.X ⁻¹' {x | ¬ featureInteractionDesign φ a x ⬝ᵥ v = 0} ∩ T.A ⁻¹' {a}) = 0 :=
      measure_mono_null (fun ω hω => by
        obtain ⟨h1, h2⟩ := hω
        simp only [Set.mem_preimage, Set.mem_ofPred_eq, Set.mem_singleton_iff] at h1 h2 ⊢
        rw [h2]; exact h1) (ae_iff.1 hv)
    rw [hT.indepFun_X_A.measure_inter_preimage_eq_mul _ _ hS (measurableSet_singleton a)]
      at h0
    have hpa : T.μ (T.A ⁻¹' {a}) ≠ 0 := by
      intro h
      have := hT.prob_arm_pos a
      rw [measureReal_def, h, ENNReal.toReal_zero] at this
      exact lt_irrefl _ this
    exact (mul_eq_zero.1 h0).resolve_right hpa
  have hf := eq_zero_of_ae_affine_of_margin hφ hδ hmargin ((harm false).mono fun x hx => by
    rw [featureInteractionDesign_dotProduct] at hx; simpa using hx)
  have ht := eq_zero_of_ae_affine_of_margin hφ hδ hmargin
    (c := interactionIntercept v + interactionEffect v)
    (w := interactionMain v + interactionModifier v) ((harm true).mono fun x hx => by
      rw [featureInteractionDesign_dotProduct] at hx; simpa [add_dotProduct] using hx)
  obtain ⟨hmain, hint⟩ := hf
  obtain ⟨hmod, heff⟩ := ht
  rw [hint, zero_add] at heff
  rw [hmain, zero_add] at hmod
  funext k
  rcases k with (_ | j) | (_ | j)
  · exact hint
  · exact congrFun hmain j
  · exact heff
  · exact congrFun hmod j

/-- **The logistic outcome model of a trial from the law of its records**, for the interaction
design of bounded measurable features with the margin condition at `t` in a randomized trial: if
the records `((X, A), Y)` have the law of the logistic family at `ξ₀`, the design is measurable,
integrable and of full rank, so the trial satisfies `Trial.LogisticOutcomeModel`. -/
theorem _root_.CausalInference.IndirectComparison.Trial.logisticOutcomeModel_featureInteraction
    [IsProbabilityMeasure T.μ] (hT : T.IsRandomizedTwoArm) (hφ : Measurable φ) {B : ℝ}
    (hB : ∀ x, ‖φ x - t‖ ≤ B) {δ : ℝ} (hδ : 0 < δ)
    (hmargin : ∀ v : Fin p → ℝ, ‖v‖ = 1 → δ ≤ T.covLaw.real {x | δ ≤ v ⬝ᵥ (φ x - t)})
    {ξ₀ : Option (Fin p) ⊕ Option (Fin p) → ℝ}
    (hlaw : T.μ.map (fun ω => ((T.X ω, T.A ω), T.obsOutcome ω)) =
      (glmFamily logisticKernel (T.μ.map fun ω => (T.X ω, T.A ω))
        (fun q => featureInteractionDesign φ q.2 q.1)
        (measurable_featureInteractionDesign_pair hφ)).law ξ₀) :
    T.LogisticOutcomeModel (fun q => featureInteractionDesign φ q.2 q.1) ξ₀ where
  measurable_z := measurable_featureInteractionDesign_pair hφ
  integrable_z j := (integrable_const (1 + B + ‖t‖)).mono'
    ((measurable_featureInteractionDesign_pair hφ j).comp
      (hT.measurable_X.prodMk hT.measurable_A)).aestronglyMeasurable
    (ae_of_all _ fun ω => by
      rw [Real.norm_eq_abs]; exact abs_featureInteractionDesign_le hB _ _ j)
  full_rank _ hv := featureInteractionDesign_eq_zero_of_ae hT hφ hδ hmargin hv
  law_eq := hlaw

/-! ### Two facts on the logistic scale -/

/-- **A mean of logistic risks lies strictly between `0` and `1`** under every probability
law. -/
theorem integral_sigmoid_mem_Ioo {ν : Measure 𝒳} [IsProbabilityMeasure ν] {f : 𝒳 → ℝ}
    (hf : Measurable f) : ∫ x, Real.sigmoid (f x) ∂ν ∈ Set.Ioo (0 : ℝ) 1 := by
  have hm : Measurable fun x => Real.sigmoid (f x) := continuous_sigmoid.measurable.comp hf
  have hi : Integrable (fun x => Real.sigmoid (f x)) ν :=
    (integrable_const (1 : ℝ)).mono' hm.aestronglyMeasurable (ae_of_all _ fun x => by
      rw [Real.norm_eq_abs, abs_of_pos (Real.sigmoid_pos _)]; exact Real.sigmoid_le_one _)
  have hpos : ∀ {g : 𝒳 → ℝ}, Integrable g ν → (∀ x, 0 < g x) → 0 < ∫ x, g x ∂ν := by
    intro g hg hgp
    rw [integral_pos_iff_support_of_nonneg (fun x => (hgp x).le) hg,
      show Function.support g = Set.univ from Set.eq_univ_of_forall fun x => (hgp x).ne']
    simp
  refine ⟨hpos hi fun x => Real.sigmoid_pos _, ?_⟩
  have h1 := hpos (g := fun x => 1 - Real.sigmoid (f x)) ((integrable_const (1 : ℝ)).sub hi)
    fun x => sub_pos.2 (Real.sigmoid_lt_one (f x))
  rw [integral_sub (integrable_const _) hi, integral_const, probReal_univ, one_smul] at h1
  linarith

/-- **The tilted covariate law of entropy balancing is a probability law**: the trial covariate
law with the density `w₀ / ∫ w₀`, for the population tilt `w₀` of bounded measurable features in a
randomized trial. -/
theorem isProbabilityMeasure_entropyTiltedLaw [IsProbabilityMeasure T.μ]
    (hT : T.IsRandomizedTwoArm) (hφ : Measurable φ) {B : ℝ} (hB : ∀ x, ‖φ x - t‖ ≤ B) :
    IsProbabilityMeasure (commonLimitFollowUpTilted T φ t) := by
  have h := commonLimitFollowUp_integral_tiltedCovLaw (T := T) (t := t) hφ fun _ => (1 : ℝ)
  have hZ := commonLimitFollowUp_integral_trialTilt_pos hT hφ hB
  simp only [integral_const, smul_eq_mul, mul_one, div_self hZ.ne'] at h
  exact ⟨ENNReal.toReal_eq_one_iff _ |>.1 (by rw [← measureReal_def]; exact h)⟩

namespace MultilevelModel

variable {J K : Type*}

omit [MeasurableSpace 𝒳] in
/-- The logistic risk of the interaction design at `ipdCoef M μ a c` is the multilevel surface
`σ(η_k(φ(x)))` at the baseline `μ`, with `k = a` on the arm `true` and `k = c` on the arm
`false`. -/
theorem sigmoid_featureInteractionDesign_ipdCoef (M : MultilevelModel J K p) (μ : ℝ) (a c : K)
    (e : Bool) (x : 𝒳) :
    Real.sigmoid (featureInteractionDesign φ e x ⬝ᵥ M.ipdCoef μ a c) =
      M.surface Real.sigmoid μ (if e then a else c) (φ x) := by
  rw [featureInteractionDesign_dotProduct_ipdCoef]
  rfl

/-- The mean of the logistic risk at `ipdCoef M μ a c` under a covariate law `ν` is the mean of
the multilevel surface under the feature law `ν ∘ φ⁻¹`. -/
theorem integral_sigmoid_ipdCoef (M : MultilevelModel J K p) (μ : ℝ) (a c : K) (e : Bool)
    (hφ : Measurable φ) (ν : Measure 𝒳) :
    ∫ x, Real.sigmoid (featureInteractionDesign φ e x ⬝ᵥ M.ipdCoef μ a c) ∂ν =
      ∫ u, M.surface Real.sigmoid μ (if e then a else c) u ∂(ν.map φ) := by
  simp only [sigmoid_featureInteractionDesign_ipdCoef]
  rw [integral_map hφ.aemeasurable
    (M.measurable_surface continuous_sigmoid.measurable μ _).aestronglyMeasurable]

/-- **The regression of a trial with the multilevel logistic model is the multilevel surface.**
In a randomized trial whose records have the law of the logistic family at `ipdCoef M μ_T a c`
in the interaction design of bounded measurable features with the margin condition at `t`, the
regression of the outcome on the covariates and the arm is `σ(η_k(φ(x)))` at the baseline
`μ_T`. -/
theorem isOutcomeRegression_surface_sigmoid [IsProbabilityMeasure T.μ]
    (M : MultilevelModel J K p) {μT : ℝ} {a c : K} (hT : T.IsRandomizedTwoArm)
    (hφ : Measurable φ) {B : ℝ} (hB : ∀ x, ‖φ x - t‖ ≤ B) {δ : ℝ} (hδ : 0 < δ)
    (hmargin : ∀ v : Fin p → ℝ, ‖v‖ = 1 → δ ≤ T.covLaw.real {x | δ ≤ v ⬝ᵥ (φ x - t)})
    (hlawM : T.μ.map (fun ω => ((T.X ω, T.A ω), T.obsOutcome ω)) =
      (glmFamily logisticKernel (T.μ.map fun ω => (T.X ω, T.A ω))
        (fun q => featureInteractionDesign φ q.2 q.1)
        (measurable_featureInteractionDesign_pair hφ)).law (M.ipdCoef μT a c)) :
    IsOutcomeRegression T.μ T.A T.X T.obsOutcome
      fun e x => M.surface Real.sigmoid μT (if e then a else c) (φ x) := by
  have hM := T.logisticOutcomeModel_featureInteraction hT hφ hB hδ hmargin hlawM
  have h := hM.isOutcomeRegression hT (hM.integrable_Y hT)
  simpa only [sigmoid_featureInteractionDesign_ipdCoef] using h

/-! ### The limits of the two estimators -/

variable {Q : Population Ω₂ 𝒳 ι} {P : Measure Ξ} {O : ℕ → Ξ → (𝒳 × Bool) × ℝ}
  {Kc : Set (Option (Fin p) ⊕ Option (Fin p) → ℝ)}

/-- **The multilevel model with the logit link: the limits of the logistic fit, of
standardization and of weighting.** Let the trial of `a` (arm `true`) against `c` (arm `false`)
be randomized, with records `((X, A), Y)` whose law is the logistic family at `ipdCoef M μ_T a c`
in the interaction design of bounded measurable features `φ` with the margin condition at `t`:
`P(Y = 1 | x, k) = σ(η_k(φ(x)))` at the baseline `μ_T`. Let `O` be a measurable i.i.d. sample of
the records, the fit taken over a compact `K ∋ ipdCoef M μ_T a c`, and `Q` a target with
measurable covariates. Then:

* the logistic maximum likelihood fit converges in probability to `ipdCoef M μ_T a c`;
* the standardized marginal log odds ratio of `a` against `c` under `Q_X` converges in
  probability to `linkMarginal logit (Q_X ∘ φ⁻¹) (σ ∘ η_c) (σ ∘ η_a)`, the marginal log odds
  ratio of the multilevel surfaces at `μ_T` under the target feature law;
* the weighted log odds ratio `logit μ̂_true - logit μ̂_false` of the same sample, with the entropy
  balancing weights at `t`, converges in probability to the same functional under the tilted
  covariate law `T_X^tilt` of entropy balancing, the trial covariate law with the density
  proportional to the population tilt `exp(β₀ᵀ(φ(x) - t))`;
* the tilted law has the feature means `t`.

So weighting estimates the multilevel marginal log odds ratio under a law with the right feature
means, which is in general not the target law; the two limits agree when the risks are affine in
the features (`commonLimit_logit_of_affine`). The logistic outcome model of the trial, the
integrability of its outcomes, its regression and the positivity of the two limiting risks below
`1`, which makes the logit continuous there, are all derived. -/
theorem commonLimit_logit [IsProbabilityMeasure T.μ] [IsProbabilityMeasure P]
    [IsProbabilityMeasure Q.μ] (M : MultilevelModel J K p) {μT : ℝ} {a c : K}
    (hT : T.IsRandomizedTwoArm) (hφ : Measurable φ) {B : ℝ} (hB : ∀ x, ‖φ x - t‖ ≤ B) {δ : ℝ}
    (hδ : 0 < δ)
    (hmargin : ∀ v : Fin p → ℝ, ‖v‖ = 1 → δ ≤ T.covLaw.real {x | δ ≤ v ⬝ᵥ (φ x - t)})
    (hlawM : T.μ.map (fun ω => ((T.X ω, T.A ω), T.obsOutcome ω)) =
      (glmFamily logisticKernel (T.μ.map fun ω => (T.X ω, T.A ω))
        (fun q => featureInteractionDesign φ q.2 q.1)
        (measurable_featureInteractionDesign_pair hφ)).law (M.ipdCoef μT a c))
    (hK : IsCompact Kc) (hξ : M.ipdCoef μT a c ∈ Kc) (hO : IsIIDSample O P)
    (hOm : ∀ i, Measurable (O i))
    (hlaw : P.map (O 0) = T.μ.map fun ω => ((T.X ω, T.A ω), T.obsOutcome ω))
    (hX₂ : Measurable Q.X) :
    TendstoInMeasure P (glmMLE logisticDens (fun q => featureInteractionDesign φ q.2 q.1) Kc O)
      atTop (fun _ => M.ipdCoef μT a c) ∧
    TendstoInMeasure P (fun n ω => linkMarginal logit Q.covLaw
        (fun x => Real.sigmoid (featureInteractionDesign φ false x ⬝ᵥ
          glmMLE logisticDens (fun q => featureInteractionDesign φ q.2 q.1) Kc O n ω))
        (fun x => Real.sigmoid (featureInteractionDesign φ true x ⬝ᵥ
          glmMLE logisticDens (fun q => featureInteractionDesign φ q.2 q.1) Kc O n ω)))
      atTop (fun _ => linkMarginal logit (Q.covLaw.map φ) (M.surface Real.sigmoid μT c)
        (M.surface Real.sigmoid μT a)) ∧
    TendstoInMeasure P (fun n ω =>
        logit (sampleBalancedArmMean φ t (fun i ω => commonLimitReassoc (O i ω)) true n ω) -
        logit (sampleBalancedArmMean φ t (fun i ω => commonLimitReassoc (O i ω)) false n ω))
      atTop (fun _ => linkMarginal logit ((commonLimitFollowUpTilted T φ t).map φ)
        (M.surface Real.sigmoid μT c) (M.surface Real.sigmoid μT a)) ∧
    ∀ k, ∫ x, φ x k ∂commonLimitFollowUpTilted T φ t = t k := by
  have hM := T.logisticOutcomeModel_featureInteraction hT hφ hB hδ hmargin hlawM
  have hYi := hM.integrable_Y hT
  have hfit := hM.tendstoInMeasure hT hK hξ hO hlaw
  have : IsProbabilityMeasure Q.covLaw := Q.isProbabilityMeasure_covLaw hX₂
  have hη : ∀ e, Measurable fun x => featureInteractionDesign φ e x ⬝ᵥ M.ipdCoef μT a c :=
    fun e => Finset.measurable_sum _ fun k _ =>
      (measurable_featureInteractionDesign hφ e k).mul_const _
  have hS : ∀ e, TendstoInMeasure P (fun n ω => ∫ x, Real.sigmoid (featureInteractionDesign φ e x ⬝ᵥ
      glmMLE logisticDens (fun q => featureInteractionDesign φ q.2 q.1) Kc O n ω) ∂Q.covLaw)
      atTop (fun _ => ∫ x, Real.sigmoid (featureInteractionDesign φ e x ⬝ᵥ M.ipdCoef μT a c)
        ∂Q.covLaw) := fun e => by
    have hr := logisticSurface_regular hM.measurable_z e Q.covLaw
    exact tendstoInMeasure_integral_of_dominated
      (h := fun ξ x => Real.sigmoid (featureInteractionDesign φ e x ⬝ᵥ ξ))
      (Eventually.of_forall fun ξ => (hr.1 ξ).aestronglyMeasurable) hr.2.1
      (Eventually.of_forall fun ξ => ae_of_all _ (hr.2.2.1 ξ))
      (ae_of_all _ fun x => (hr.2.2.2 x).continuousAt) hfit
  have hSl : ∀ e, ContinuousAt logit
      (∫ x, Real.sigmoid (featureInteractionDesign φ e x ⬝ᵥ M.ipdCoef μT a c) ∂Q.covLaw) :=
    fun e => continuousAt_logit (integral_sigmoid_mem_Ioo (hη e))
  have hS2 := ((hS true).comp_continuousAt (hSl true)).sub
    ((hS false).comp_continuousAt (hSl false))
  rw [integral_sigmoid_ipdCoef M μT a c true hφ, integral_sigmoid_ipdCoef M μT a c false hφ]
    at hS2
  have hreg := M.isOutcomeRegression_surface_sigmoid hT hφ hB hδ hmargin hlawM
  have hrec : Measurable fun ω => ((T.X ω, T.A ω), T.obsOutcome ω) :=
    (hT.measurable_X.prodMk hT.measurable_A).prodMk
      (measurable_obsOutcome hT.measurable_A hT.measurable_Y)
  have hlaw' : P.map (fun ω => commonLimitReassoc (O 0 ω)) = T.ipdLaw := by
    rw [show (fun ω => commonLimitReassoc (O 0 ω)) = commonLimitReassoc ∘ O 0 from rfl,
      ← Measure.map_map measurable_commonLimitReassoc (hOm 0), hlaw,
      Measure.map_map measurable_commonLimitReassoc hrec]
    rfl
  have hW : ∀ e : Bool, TendstoInMeasure P
      (sampleBalancedArmMean φ t (fun i ω => commonLimitReassoc (O i ω)) e) atTop
      (fun _ => ∫ x, M.surface Real.sigmoid μT (if e then a else c) (φ x)
        ∂commonLimitFollowUpTilted T φ t) := fun e =>
    commonLimitFollowUp_tendstoInMeasure_weighted hT hYi hreg
      (hO.comp measurable_commonLimitReassoc) hlaw' hφ hB hδ hmargin e
  have : IsProbabilityMeasure (commonLimitFollowUpTilted T φ t) :=
    isProbabilityMeasure_entropyTiltedLaw hT hφ hB
  have hWl : ∀ e : Bool, ContinuousAt logit
      (∫ x, M.surface Real.sigmoid μT (if e then a else c) (φ x)
        ∂commonLimitFollowUpTilted T φ t) := fun e =>
    continuousAt_logit (integral_sigmoid_mem_Ioo ((M.continuous_eta μT _).measurable.comp hφ))
  have hW2 := ((hW true).comp_continuousAt (hWl true)).sub
    ((hW false).comp_continuousAt (hWl false))
  have hmap : ∀ k, ∫ x, M.surface Real.sigmoid μT k (φ x) ∂commonLimitFollowUpTilted T φ t =
      ∫ u, M.surface Real.sigmoid μT k u ∂((commonLimitFollowUpTilted T φ t).map φ) := fun k =>
    (integral_map hφ.aemeasurable
      (M.measurable_surface continuous_sigmoid.measurable μT k).aestronglyMeasurable).symm
  simp only [ite_true, Bool.false_eq_true, ite_false, hmap] at hW2
  exact ⟨hfit, hS2, hW2,
    commonLimitFollowUp_integral_feature_tiltedCovLaw hT hφ hB hδ hmargin⟩

/-- **When the risks are affine in the features, weighting and standardization share the
multilevel limit.** Under the hypotheses of `commonLimit_logit`, let `t` be the target feature
mean and let the multilevel risk of each arm be affine in the features,
`σ(η_k(φ(x))) = α_k + β_kᵀφ(x)` for every `x` (`k = a` on the arm `true`, `k = c` on the arm
`false`). Then the standardized marginal log odds ratio and the weighted log odds ratio both
converge in probability to the marginal log odds ratio of the multilevel surfaces under the target
feature law, which is `logit(α_a + β_aᵀt) - logit(α_c + β_cᵀt)`, and their difference converges
in probability to `0`. The affinity holds for every model when the features take two values. -/
theorem commonLimit_logit_of_affine [IsProbabilityMeasure T.μ] [IsProbabilityMeasure P]
    [IsProbabilityMeasure Q.μ] (M : MultilevelModel J K p) {μT : ℝ} {a c : K}
    (hT : T.IsRandomizedTwoArm) (hφ : Measurable φ) {B : ℝ} (hB : ∀ x, ‖φ x - t‖ ≤ B) {δ : ℝ}
    (hδ : 0 < δ)
    (hmargin : ∀ v : Fin p → ℝ, ‖v‖ = 1 → δ ≤ T.covLaw.real {x | δ ≤ v ⬝ᵥ (φ x - t)})
    (hlawM : T.μ.map (fun ω => ((T.X ω, T.A ω), T.obsOutcome ω)) =
      (glmFamily logisticKernel (T.μ.map fun ω => (T.X ω, T.A ω))
        (fun q => featureInteractionDesign φ q.2 q.1)
        (measurable_featureInteractionDesign_pair hφ)).law (M.ipdCoef μT a c))
    (hK : IsCompact Kc) (hξ : M.ipdCoef μT a c ∈ Kc) (hO : IsIIDSample O P)
    (hOm : ∀ i, Measurable (O i))
    (hlaw : P.map (O 0) = T.μ.map fun ω => ((T.X ω, T.A ω), T.obsOutcome ω))
    (hX₂ : Measurable Q.X) (ht : ∀ k, ∫ x, φ x k ∂Q.covLaw = t k) {α : Bool → ℝ}
    {β : Bool → Fin p → ℝ}
    (haff : ∀ e x, M.surface Real.sigmoid μT (if e then a else c) (φ x) = α e + β e ⬝ᵥ φ x) :
    TendstoInMeasure P (fun n ω => linkMarginal logit Q.covLaw
        (fun x => Real.sigmoid (featureInteractionDesign φ false x ⬝ᵥ
          glmMLE logisticDens (fun q => featureInteractionDesign φ q.2 q.1) Kc O n ω))
        (fun x => Real.sigmoid (featureInteractionDesign φ true x ⬝ᵥ
          glmMLE logisticDens (fun q => featureInteractionDesign φ q.2 q.1) Kc O n ω)))
      atTop (fun _ => linkMarginal logit (Q.covLaw.map φ) (M.surface Real.sigmoid μT c)
        (M.surface Real.sigmoid μT a)) ∧
    TendstoInMeasure P (fun n ω =>
        logit (sampleBalancedArmMean φ t (fun i ω => commonLimitReassoc (O i ω)) true n ω) -
        logit (sampleBalancedArmMean φ t (fun i ω => commonLimitReassoc (O i ω)) false n ω))
      atTop (fun _ => linkMarginal logit (Q.covLaw.map φ) (M.surface Real.sigmoid μT c)
        (M.surface Real.sigmoid μT a)) ∧
    TendstoInMeasure P (fun n ω => linkMarginal logit Q.covLaw
        (fun x => Real.sigmoid (featureInteractionDesign φ false x ⬝ᵥ
          glmMLE logisticDens (fun q => featureInteractionDesign φ q.2 q.1) Kc O n ω))
        (fun x => Real.sigmoid (featureInteractionDesign φ true x ⬝ᵥ
          glmMLE logisticDens (fun q => featureInteractionDesign φ q.2 q.1) Kc O n ω)) -
        (logit (sampleBalancedArmMean φ t (fun i ω => commonLimitReassoc (O i ω)) true n ω) -
          logit (sampleBalancedArmMean φ t (fun i ω => commonLimitReassoc (O i ω)) false n ω)))
      atTop (fun _ => 0) ∧
    linkMarginal logit (Q.covLaw.map φ) (M.surface Real.sigmoid μT c)
        (M.surface Real.sigmoid μT a) =
      logit (α true + β true ⬝ᵥ t) - logit (α false + β false ⬝ᵥ t) := by
  obtain ⟨-, hS, hW, -⟩ := M.commonLimit_logit hT hφ hB hδ hmargin hlawM hK hξ hO hOm hlaw hX₂
  have hmap : ∀ (ν : Measure 𝒳) (k : K), ∫ u, M.surface Real.sigmoid μT k u ∂(ν.map φ) =
      ∫ x, M.surface Real.sigmoid μT k (φ x) ∂ν := fun ν k =>
    integral_map hφ.aemeasurable
      (M.measurable_surface continuous_sigmoid.measurable μT k).aestronglyMeasurable
  have hQ : ∀ e : Bool, ∫ x, M.surface Real.sigmoid μT (if e then a else c) (φ x) ∂Q.covLaw =
      α e + β e ⬝ᵥ t := fun e => integral_affine_covLaw hφ hB ht (haff e)
  have hT' : ∀ e : Bool, ∫ x, M.surface Real.sigmoid μT (if e then a else c) (φ x)
      ∂commonLimitFollowUpTilted T φ t = α e + β e ⬝ᵥ t := fun e =>
    commonLimitFollowUp_integral_affine_tiltedCovLaw hT hφ hB hδ hmargin (haff e)
  have hval : linkMarginal logit (Q.covLaw.map φ) (M.surface Real.sigmoid μT c)
      (M.surface Real.sigmoid μT a) =
      logit (α true + β true ⬝ᵥ t) - logit (α false + β false ⬝ᵥ t) := by
    simp only [linkMarginal, hmap]
    rw [← hQ true, ← hQ false]
    rfl
  have hval' : linkMarginal logit ((commonLimitFollowUpTilted T φ t).map φ)
      (M.surface Real.sigmoid μT c) (M.surface Real.sigmoid μT a) =
      logit (α true + β true ⬝ᵥ t) - logit (α false + β false ⬝ᵥ t) := by
    simp only [linkMarginal, hmap]
    rw [← hT' true, ← hT' false]
    rfl
  rw [hval', ← hval] at hW
  exact ⟨hS, hW, tendstoInMeasure_sub_zero_of_same_limit hS hW, hval⟩

/-- **The standardized limit is the target marginal log odds ratio when the target follows the
multilevel model at the trial baseline.** Under the hypotheses of `commonLimit_logit`, let the
conditional risks of `Y(s_a)` and `Y(s_c)` in the target be the multilevel surfaces of `a` and `c`
at the trial baseline `μ_T`, with integrable potential outcomes. Then the standardized marginal
log odds ratio converges in probability to the target marginal log odds ratio of `s_a` against
`s_c`. At a target baseline `α_Q ≠ μ_T`
the target marginal log odds ratio is in general another number: on the logit scale the
baseline does not cancel. -/
theorem commonLimit_logit_marginalEffect [IsProbabilityMeasure T.μ] [IsProbabilityMeasure P]
    [IsProbabilityMeasure Q.μ] (M : MultilevelModel J K p) {μT : ℝ} {a c : K}
    (hT : T.IsRandomizedTwoArm) (hφ : Measurable φ) {B : ℝ} (hB : ∀ x, ‖φ x - t‖ ≤ B) {δ : ℝ}
    (hδ : 0 < δ)
    (hmargin : ∀ v : Fin p → ℝ, ‖v‖ = 1 → δ ≤ T.covLaw.real {x | δ ≤ v ⬝ᵥ (φ x - t)})
    (hlawM : T.μ.map (fun ω => ((T.X ω, T.A ω), T.obsOutcome ω)) =
      (glmFamily logisticKernel (T.μ.map fun ω => (T.X ω, T.A ω))
        (fun q => featureInteractionDesign φ q.2 q.1)
        (measurable_featureInteractionDesign_pair hφ)).law (M.ipdCoef μT a c))
    (hK : IsCompact Kc) (hξ : M.ipdCoef μT a c ∈ Kc) (hO : IsIIDSample O P)
    (hOm : ∀ i, Measurable (O i))
    (hlaw : P.map (O 0) = T.μ.map fun ω => ((T.X ω, T.A ω), T.obsOutcome ω))
    (hX₂ : Measurable Q.X) {sa sc : ι} (hYa : Integrable (Q.Y sa) Q.μ)
    (hYc : Integrable (Q.Y sc) Q.μ)
    (ha : Q.IsCondMean sa fun x => M.surface Real.sigmoid μT a (φ x))
    (hc : Q.IsCondMean sc fun x => M.surface Real.sigmoid μT c (φ x)) :
    TendstoInMeasure P (fun n ω => linkMarginal logit Q.covLaw
        (fun x => Real.sigmoid (featureInteractionDesign φ false x ⬝ᵥ
          glmMLE logisticDens (fun q => featureInteractionDesign φ q.2 q.1) Kc O n ω))
        (fun x => Real.sigmoid (featureInteractionDesign φ true x ⬝ᵥ
          glmMLE logisticDens (fun q => featureInteractionDesign φ q.2 q.1) Kc O n ω)))
      atTop (fun _ => Q.marginalEffect logit sc sa) := by
  obtain ⟨-, hS, -, -⟩ := M.commonLimit_logit hT hφ hB hδ hmargin hlawM hK hξ hO hOm hlaw hX₂
  have he := Population.marginalEffect_eq_linkMarginal logit hX₂ hYc hYa hc ha
  have hmap : ∀ k : K, ∫ u, M.surface Real.sigmoid μT k u ∂(Q.covLaw.map φ) =
      ∫ x, M.surface Real.sigmoid μT k (φ x) ∂Q.covLaw := fun k =>
    integral_map hφ.aemeasurable
      (M.measurable_surface continuous_sigmoid.measurable μT k).aestronglyMeasurable
  have hval : linkMarginal logit (Q.covLaw.map φ) (M.surface Real.sigmoid μT c)
      (M.surface Real.sigmoid μT a) = Q.marginalEffect logit sc sa := by
    rw [he]
    simp only [linkMarginal, hmap]
  rwa [hval] at hS

end MultilevelModel

end NetworkMetaRegression

end CausalInference
