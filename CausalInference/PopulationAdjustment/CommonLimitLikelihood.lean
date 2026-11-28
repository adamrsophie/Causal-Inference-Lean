/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.PopulationAdjustment.CommonLimitLinear
public import CausalInference.PopulationAdjustment.StandardizationConsistencyLogistic

/-!
# The common limit with the likelihood fit

The weighted estimator and standardization with the logistic maximum likelihood fit
(`glmMLE logisticDens`) computed from one sample of the trial records. The likelihood fit reads
the records as `((X, A), Y)`, the weighted estimator as `(X, A, Y)`; the two are the same sample
reassociated (`commonLimitReassoc`), so both estimators use the same data.

In a randomized trial with a logistic outcome model (`Trial.LogisticOutcomeModel`), the observed
outcome is almost surely `0` or `1` (`Trial.LogisticOutcomeModel.ae_obsOutcome`); randomization
carries this over to every potential outcome, so the potential outcomes are integrable and the
squared residual of the records is at most `1`. The conditions of both consistency theorems are
then derived. The two estimators of the target mean of `Y(s)` share their limit when the logistic
regression `σ(z(x, a) ⬝ ξ₀)` of the arm is affine in the matched features `φ`, which holds for
saturated features (for instance the indicators of the cells of a finite covariate); otherwise
they can differ (`CommonLimitDiffer`).

The Gaussian likelihood is not covered: the consistency theorem of the generalized linear fit
(`tendstoInMeasure_glmMLE`) asks for a bound `|log dens(η, y)| ≤ a(y) + b|η|` linear in the
linear predictor, which the normal log density, quadratic in `η`, does not satisfy. The least
squares fit, which is the normal maximum likelihood fit, is treated in `CommonLimitLinear`.

## Main definitions

* `commonLimitReassoc`: the records `((x, a), y) ↦ (x, a, y)`.

## Main results

* `Trial.LogisticOutcomeModel.ae_obsOutcome`, `Trial.LogisticOutcomeModel.ae_potentialOutcome`:
  binary outcomes.
* `commonLimit_logistic_armMean`: both estimators converge in probability to the target mean,
  and their difference converges in probability to `0`.
* `commonLimit_logistic_linkMarginal`: the same for the marginal effect on a link scale.

## References

* J. E. Signorovitch and coauthors, PharmacoEconomics 28 (2010).
* D. M. Phillippo, A. E. Ades, S. Dias, S. Palmer, K. R. Abrams and N. J. Welton, *Methods for
  population-adjusted indirect comparisons in health technology appraisal*, Medical Decision
  Making 38 (2018).
-/

@[expose] public section

namespace CausalInference

namespace PopulationAdjustment

open MeasureTheory ProbabilityTheory Filter Topology Matrix EffectMeasure IndirectComparison
  PointTreatment Transport

/-- The records `((x, a), y)` of the likelihood fit as the records `(x, a, y)` of the weighted
estimator. -/
def commonLimitReassoc {𝒳 : Type*} (q : (𝒳 × Bool) × ℝ) : 𝒳 × Bool × ℝ :=
  (q.1.1, q.1.2, q.2)

theorem measurable_commonLimitReassoc {𝒳 : Type*} [MeasurableSpace 𝒳] :
    Measurable (commonLimitReassoc (𝒳 := 𝒳)) :=
  measurable_fst.fst.prodMk (measurable_fst.snd.prodMk measurable_snd)

section Binary

theorem measurableSet_zero_one : MeasurableSet ({0, 1} : Set ℝ) :=
  (measurableSet_singleton 1).insert 0

variable {Ω₁ 𝒳 κ : Type*} [MeasurableSpace Ω₁] [MeasurableSpace 𝒳] [Fintype κ]
  {T : Trial Ω₁ 𝒳 Bool} {z : 𝒳 × Bool → κ → ℝ} {ξ₀ : κ → ℝ}

/-- **The outcome of a logistic outcome model is binary**: the law of the records is dominated
by the design law times counting measure on `{0, 1}`. -/
theorem _root_.CausalInference.IndirectComparison.Trial.LogisticOutcomeModel.ae_obsOutcome
    [IsProbabilityMeasure T.μ] (hM : T.LogisticOutcomeModel z ξ₀) (hT : T.IsRandomizedTwoArm) :
    ∀ᵐ ω ∂T.μ, T.obsOutcome ω = 0 ∨ T.obsOutcome ω = 1 := by
  set S : Set ((𝒳 × Bool) × ℝ) := Prod.snd ⁻¹' ({0, 1} : Set ℝ)ᶜ with hS
  have hSm : MeasurableSet S :=
    measurable_snd (measurableSet_zero_one).compl
  have hrec : Measurable fun ω => ((T.X ω, T.A ω), T.obsOutcome ω) :=
    (hT.measurable_X.prodMk hT.measurable_A).prodMk
      (measurable_obsOutcome hT.measurable_A hT.measurable_Y)
  have hν : ((T.μ.map fun ω => (T.X ω, T.A ω)).prod logisticKernel.lam) S = 0 := by
    rw [hS, ← Set.univ_prod, Measure.prod_prod]
    have h0 : logisticKernel.lam ({0, 1} : Set ℝ)ᶜ = 0 := by
      change (Measure.dirac (0 : ℝ) + Measure.dirac (1 : ℝ)) ({0, 1} : Set ℝ)ᶜ = 0
      rw [add_apply, Measure.dirac_apply' _ (measurableSet_zero_one).compl,
        Measure.dirac_apply' _ (measurableSet_zero_one).compl]
      simp
    rw [h0, mul_zero]
  have hlaw : (T.μ.map fun ω => ((T.X ω, T.A ω), T.obsOutcome ω)) S = 0 := by
    rw [hM.law_eq]
    exact withDensity_absolutelyContinuous _ _ hν
  rw [Measure.map_apply hrec hSm] at hlaw
  refine measure_mono_null (fun ω hω => ?_) hlaw
  have hω' : ¬(T.obsOutcome ω = 0 ∨ T.obsOutcome ω = 1) := hω
  rw [not_or] at hω'
  simp [hS, hω'.1, hω'.2]

/-- **Every potential outcome of a randomized trial with a logistic outcome model is binary**:
the event `Y(t) ∉ {0, 1}` is independent of the arm, and on the arm `t` it is the event that the
observed outcome is not binary. -/
theorem _root_.CausalInference.IndirectComparison.Trial.LogisticOutcomeModel.ae_potentialOutcome
    [IsProbabilityMeasure T.μ] (hM : T.LogisticOutcomeModel z ξ₀) (hT : T.IsRandomizedTwoArm)
    (t : Bool) : ∀ᵐ ω ∂T.μ, T.Y t ω = 0 ∨ T.Y t ω = 1 := by
  set E : Set (𝒳 × ℝ × ℝ) := (fun q => if t then q.2.2 else q.2.1) ⁻¹' ({0, 1} : Set ℝ)ᶜ
    with hE
  have hEm : MeasurableSet E := by
    refine (show Measurable fun q : 𝒳 × ℝ × ℝ => if t then q.2.2 else q.2.1 from ?_)
      (measurableSet_zero_one).compl
    cases t
    · exact measurable_snd.fst
    · exact measurable_snd.snd
  have hinter : T.μ (T.A ⁻¹' {t} ∩ (fun ω => (T.X ω, potentialPair T.Y ω)) ⁻¹' E) = 0 := by
    refine measure_mono_null (fun ω hω => ?_) (ae_iff.1 (hM.ae_obsOutcome hT))
    obtain ⟨h1, h2⟩ := hω
    simp only [Set.mem_preimage, Set.mem_singleton_iff] at h1
    simp only [hE, Set.mem_preimage, Set.mem_compl_iff, Set.mem_insert_iff,
      Set.mem_singleton_iff, not_or, potentialPair] at h2
    simp only [Set.mem_ofPred_eq, not_or, Trial.obsOutcome, h1]
    cases t <;> simpa using h2
  rw [hT.indepFun.measure_inter_preimage_eq_mul _ _ (measurableSet_singleton t) hEm] at hinter
  have hpa : T.μ (T.A ⁻¹' {t}) ≠ 0 := by
    intro h
    have := hT.prob_arm_pos t
    rw [measureReal_def, h, ENNReal.toReal_zero] at this
    exact lt_irrefl _ this
  refine measure_mono_null (fun ω hω => ?_) ((mul_eq_zero.1 hinter).resolve_left hpa)
  simp only [hE, Set.mem_preimage, Set.mem_compl_iff, Set.mem_insert_iff,
    Set.mem_singleton_iff, not_or, potentialPair]
  cases t <;> simpa using hω

/-- The potential outcomes of a randomized trial with a logistic outcome model are integrable. -/
theorem _root_.CausalInference.IndirectComparison.Trial.LogisticOutcomeModel.integrable_Y
    [IsProbabilityMeasure T.μ] (hM : T.LogisticOutcomeModel z ξ₀) (hT : T.IsRandomizedTwoArm)
    (t : Bool) : Integrable (T.Y t) T.μ :=
  (integrable_const (1 : ℝ)).mono' (hT.measurable_Y t).aestronglyMeasurable
    ((hM.ae_potentialOutcome hT t).mono fun ω h => by rcases h with h | h <;> simp [h])

/-- **The squared residual of the logistic records is at most `1`.** -/
theorem _root_.CausalInference.IndirectComparison.Trial.LogisticOutcomeModel.ae_residual_sq_le
    [IsProbabilityMeasure T.μ] (hM : T.LogisticOutcomeModel z ξ₀) (hT : T.IsRandomizedTwoArm) :
    ∀ᵐ o ∂T.ipdLaw, (o.2.2 - Real.sigmoid (z (o.1, o.2.1) ⬝ᵥ ξ₀)) ^ 2 ≤ 1 := by
  have hf : Measurable fun ω => (T.X ω, T.A ω, T.obsOutcome ω) :=
    hT.measurable_X.prodMk (hT.measurable_A.prodMk
      (measurable_obsOutcome hT.measurable_A hT.measurable_Y))
  have hg : Measurable fun o : 𝒳 × Bool × ℝ => (o.2.2 - Real.sigmoid (z (o.1, o.2.1) ⬝ᵥ ξ₀)) ^ 2 :=
    (measurable_snd.snd.sub (continuous_sigmoid.measurable.comp
      ((measurable_dotProduct_design hM.measurable_z ξ₀).comp
        (measurable_fst.prodMk measurable_snd.fst)))).pow_const 2
  rw [Trial.ipdLaw, ae_map_iff hf.aemeasurable (measurableSet_le hg measurable_const)]
  filter_upwards [hM.ae_obsOutcome hT] with ω h
  have h0 := Real.sigmoid_pos (z (T.X ω, T.A ω) ⬝ᵥ ξ₀)
  have h1 := Real.sigmoid_lt_one (z (T.X ω, T.A ω) ⬝ᵥ ξ₀)
  rcases h with h | h <;> simp only [h] <;> nlinarith

end Binary

section CommonLimit

variable {Ω₁ Ω₂ Ξ 𝒳 ι κ : Type*} [MeasurableSpace Ω₁] [MeasurableSpace Ω₂] [MeasurableSpace Ξ]
  [MeasurableSpace 𝒳] [Fintype κ] {p : ℕ} {T : Trial Ω₁ 𝒳 Bool} {Q : Population Ω₂ 𝒳 ι}
  {P : Measure Ξ} {O : ℕ → Ξ → (𝒳 × Bool) × ℝ} {z : 𝒳 × Bool → κ → ℝ} {ξ₀ : κ → ℝ}
  {K : Set (κ → ℝ)} {φ : 𝒳 → Fin p → ℝ} {t : Fin p → ℝ}

/-- **Weighting and standardization with the logistic fit share their limit: the target arm
mean.** Let `T` be a randomized trial with a logistic outcome model at `ξ₀`, `O` a measurable
i.i.d. sample of its records `((X, A), Y)`, the fit taken over a compact `K ∋ ξ₀`; let `φ` be
bounded measurable features with the margin condition at `t` for the trial covariate law, and let
the logistic regression of arm `a` be affine in the features,
`σ(z(x, a) ⬝ ξ₀) = α + βᵀφ(x)`. Let `Q` be a target with probability law, measurable covariates,
feature means `t`, integrable `Y(s)`, absolute constancy of arm `a` to treatment `s`, and overlap.
Then the weighted arm mean of the same sample and the standardized logistic fit both converge in
probability to `E_Q[Y(s)]`, and their difference converges in probability to `0`. -/
theorem commonLimit_logistic_armMean [IsProbabilityMeasure T.μ] [IsProbabilityMeasure P]
    [IsProbabilityMeasure Q.μ] (hT : T.IsRandomizedTwoArm) (hM : T.LogisticOutcomeModel z ξ₀)
    (hK : IsCompact K) (hξ₀ : ξ₀ ∈ K) (hO : IsIIDSample O P) (hOm : ∀ i, Measurable (O i))
    (hlaw : P.map (O 0) = T.μ.map fun ω => ((T.X ω, T.A ω), T.obsOutcome ω))
    (hφ : Measurable φ) {B : ℝ} (hB : ∀ x, ‖φ x - t‖ ≤ B) {δ : ℝ} (hδ : 0 < δ)
    (hmargin : ∀ v : Fin p → ℝ, ‖v‖ = 1 → δ ≤ T.covLaw.real {x | δ ≤ v ⬝ᵥ (φ x - t)})
    (a : Bool) {α : ℝ} {β : Fin p → ℝ} (haff : ∀ x, Real.sigmoid (z (x, a) ⬝ᵥ ξ₀) = α + β ⬝ᵥ φ x)
    (hX₂ : Measurable Q.X) (ht : ∀ k, ∫ x, φ x k ∂Q.covLaw = t k) {s : ι}
    (hYQ : Integrable (Q.Y s) Q.μ)
    (hsi : StructurallyInvariant T.μ T.X (T.Y a) Q.μ Q.X (Q.Y s)) (hov : Q.covLaw ≪ T.covLaw) :
    IsConsistent (sampleBalancedArmMean φ t (fun i ω => commonLimitReassoc (O i ω)) a)
      (Q.armMean s) P ∧
      TendstoInMeasure P (fun n ω => ∫ x, Real.sigmoid (z (x, a) ⬝ᵥ glmMLE logisticDens z K O n ω)
        ∂Q.covLaw) atTop (fun _ => Q.armMean s) ∧
      TendstoInMeasure P (fun n ω => ∫ x, Real.sigmoid (z (x, a) ⬝ᵥ glmMLE logisticDens z K O n ω)
        ∂Q.covLaw - sampleBalancedArmMean φ t (fun i ω => commonLimitReassoc (O i ω)) a n ω)
        atTop (fun _ => 0) := by
  have : IsProbabilityMeasure Q.covLaw := Q.isProbabilityMeasure_covLaw hX₂
  have hYi := hM.integrable_Y hT
  have hreg := hM.isOutcomeRegression hT hYi
  have hYo := measurable_obsOutcome hT.measurable_A hT.measurable_Y
  have hmu : ∀ e, Measurable fun x => Real.sigmoid (z (x, e) ⬝ᵥ ξ₀) := fun e =>
    (logisticSurface_regular hM.measurable_z e Q.covLaw).1 ξ₀
  -- the standardized fit
  have hr := logisticSurface_regular hM.measurable_z a Q.covLaw
  have hS := tendstoInMeasure_integral_fit_armMean
    (h := fun ξ e x => Real.sigmoid (z (x, e) ⬝ᵥ ξ)) hT hYi hreg hX₂ hYQ hsi hov
    (Eventually.of_forall fun ξ => (hr.1 ξ).aestronglyMeasurable) hr.2.1
    (Eventually.of_forall fun ξ => ae_of_all _ (hr.2.2.1 ξ))
    (ae_of_all _ fun x => (hr.2.2.2 x).continuousAt) (hM.tendstoInMeasure hT hK hξ₀ hO hlaw)
  -- the weighted estimator on the same sample
  have hrec : Measurable fun ω => ((T.X ω, T.A ω), T.obsOutcome ω) :=
    (hT.measurable_X.prodMk hT.measurable_A).prodMk hYo
  have hlaw' : P.map (fun ω => commonLimitReassoc (O 0 ω)) = T.ipdLaw := by
    rw [show (fun ω => commonLimitReassoc (O 0 ω)) = commonLimitReassoc ∘ O 0 from rfl,
      ← Measure.map_map measurable_commonLimitReassoc (hOm 0), hlaw,
      Measure.map_map measurable_commonLimitReassoc hrec]
    rfl
  have hle := hM.ae_residual_sq_le hT
  have hgm : Measurable fun o : 𝒳 × Bool × ℝ => (o.2.2 - Real.sigmoid (z (o.1, o.2.1) ⬝ᵥ ξ₀)) ^ 2 :=
    (measurable_snd.snd.sub (continuous_sigmoid.measurable.comp
      ((measurable_dotProduct_design hM.measurable_z ξ₀).comp
        (measurable_fst.prodMk measurable_snd.fst)))).pow_const 2
  have : IsProbabilityMeasure T.ipdLaw := by
    unfold Trial.ipdLaw
    exact (Measure.isProbabilityMeasure_map_iff
      (hT.measurable_X.prodMk (hT.measurable_A.prodMk hYo)).aemeasurable).2 inferInstance
  have hres2 : Integrable (fun o : 𝒳 × Bool × ℝ =>
      (o.2.2 - Real.sigmoid (z (o.1, o.2.1) ⬝ᵥ ξ₀)) ^ 2) T.ipdLaw :=
    (integrable_const (1 : ℝ)).mono' hgm.aestronglyMeasurable
      (hle.mono fun o h => by rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]; exact h)
  have hvar : T.ipdLaw[fun o => (o.2.2 - Real.sigmoid (z (o.1, o.2.1) ⬝ᵥ ξ₀)) ^ 2 |
      MeasurableSpace.comap (fun o : 𝒳 × Bool × ℝ => (o.1, o.2.1)) inferInstance]
        ≤ᵐ[T.ipdLaw] fun _ => 1 := by
    have h := condExp_mono (m := MeasurableSpace.comap
      (fun o : 𝒳 × Bool × ℝ => (o.1, o.2.1)) inferInstance) hres2 (integrable_const (1 : ℝ)) hle
    rwa [condExp_const ((measurable_fst.prodMk measurable_snd.fst).comap_le)] at h
  have hW := sampleBalancedArmMean_isConsistent_trial
    (mu := fun e x => Real.sigmoid (z (x, e) ⬝ᵥ ξ₀))
    hT.measurable_X hT.measurable_A hYo hT.indepFun_X_A (hO.comp measurable_commonLimitReassoc)
    (fun i => measurable_commonLimitReassoc.comp (hOm i)) hlaw' hφ hB hδ hmargin a
    (hT.prob_arm_pos a) hmu hres2
    (hreg.condExp_ipdLaw hT.measurable_X hT.measurable_A hYo (integrable_obsOutcome hT hYi))
    hvar haff
  -- the two limits agree
  obtain ⟨-, hval⟩ := integral_covLaw_eq_armMean_of_trial hT.measurable_X hX₂ hYQ
    (hT.isCondMean hYi hreg a) hsi hov
  have hint := integral_affine_covLaw hφ hB ht haff
  rw [← hval, hint] at hS
  rw [← hval, hint]
  exact ⟨hW, hS, tendstoInMeasure_sub_zero_of_same_limit hS hW⟩

/-- **The marginal effect on a link scale with the logistic fit.** Under the hypotheses of
`commonLimit_logistic_armMean` for the arms `true ↦ s₁` and `false ↦ s₀`, with both logistic
regressions affine in the features and a link `g` continuous at the two target means, the
weighted contrast `g(μ̂_true) - g(μ̂_false)` and the standardized contrast
`linkMarginal g Q_X (σ(z(·, false) ⬝ ξ̂)) (σ(z(·, true) ⬝ ξ̂))` of the same sample both converge in
probability to the target marginal effect `g(E_Q[Y(s₁)]) - g(E_Q[Y(s₀)])`, and their difference
converges in probability to `0`. -/
theorem commonLimit_logistic_linkMarginal [IsProbabilityMeasure T.μ] [IsProbabilityMeasure P]
    [IsProbabilityMeasure Q.μ] (hT : T.IsRandomizedTwoArm) (hM : T.LogisticOutcomeModel z ξ₀)
    (hK : IsCompact K) (hξ₀ : ξ₀ ∈ K) (hO : IsIIDSample O P) (hOm : ∀ i, Measurable (O i))
    (hlaw : P.map (O 0) = T.μ.map fun ω => ((T.X ω, T.A ω), T.obsOutcome ω))
    (hφ : Measurable φ) {B : ℝ} (hB : ∀ x, ‖φ x - t‖ ≤ B) {δ : ℝ} (hδ : 0 < δ)
    (hmargin : ∀ v : Fin p → ℝ, ‖v‖ = 1 → δ ≤ T.covLaw.real {x | δ ≤ v ⬝ᵥ (φ x - t)})
    {α : Bool → ℝ} {β : Bool → Fin p → ℝ}
    (haff : ∀ e x, Real.sigmoid (z (x, e) ⬝ᵥ ξ₀) = α e + β e ⬝ᵥ φ x)
    (hX₂ : Measurable Q.X) (ht : ∀ k, ∫ x, φ x k ∂Q.covLaw = t k) {s₀ s₁ : ι}
    (hYQ₀ : Integrable (Q.Y s₀) Q.μ) (hYQ₁ : Integrable (Q.Y s₁) Q.μ)
    (hsi₀ : StructurallyInvariant T.μ T.X (T.Y false) Q.μ Q.X (Q.Y s₀))
    (hsi₁ : StructurallyInvariant T.μ T.X (T.Y true) Q.μ Q.X (Q.Y s₁))
    (hov : Q.covLaw ≪ T.covLaw) {g : ℝ → ℝ} (hg₀ : ContinuousAt g (Q.armMean s₀))
    (hg₁ : ContinuousAt g (Q.armMean s₁)) :
    TendstoInMeasure P (fun n ω =>
        g (sampleBalancedArmMean φ t (fun i ω => commonLimitReassoc (O i ω)) true n ω) -
        g (sampleBalancedArmMean φ t (fun i ω => commonLimitReassoc (O i ω)) false n ω))
      atTop (fun _ => Q.marginalEffect g s₀ s₁) ∧
      TendstoInMeasure P (fun n ω => linkMarginal g Q.covLaw
        (fun x => Real.sigmoid (z (x, false) ⬝ᵥ glmMLE logisticDens z K O n ω))
        (fun x => Real.sigmoid (z (x, true) ⬝ᵥ glmMLE logisticDens z K O n ω)))
      atTop (fun _ => Q.marginalEffect g s₀ s₁) ∧
      TendstoInMeasure P (fun n ω => linkMarginal g Q.covLaw
        (fun x => Real.sigmoid (z (x, false) ⬝ᵥ glmMLE logisticDens z K O n ω))
        (fun x => Real.sigmoid (z (x, true) ⬝ᵥ glmMLE logisticDens z K O n ω)) -
        (g (sampleBalancedArmMean φ t (fun i ω => commonLimitReassoc (O i ω)) true n ω) -
          g (sampleBalancedArmMean φ t (fun i ω => commonLimitReassoc (O i ω)) false n ω)))
      atTop (fun _ => 0) := by
  obtain ⟨hW₀, hS₀, -⟩ := commonLimit_logistic_armMean hT hM hK hξ₀ hO hOm hlaw hφ hB hδ
    hmargin false (haff false) hX₂ ht hYQ₀ hsi₀ hov
  obtain ⟨hW₁, hS₁, -⟩ := commonLimit_logistic_armMean hT hM hK hξ₀ hO hOm hlaw hφ hB hδ
    hmargin true (haff true) hX₂ ht hYQ₁ hsi₁ hov
  have hW := (hW₁.comp_continuousAt hg₁).sub (hW₀.comp_continuousAt hg₀)
  have hS := (hS₁.comp_continuousAt hg₁).sub (hS₀.comp_continuousAt hg₀)
  exact ⟨hW, hS, tendstoInMeasure_sub_zero_of_same_limit hS hW⟩

end CommonLimit

end PopulationAdjustment

end CausalInference
