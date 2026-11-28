/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.PopulationAdjustment.IdentificationRandomizedTrial
public import CausalInference.Estimation.ConvergenceInProbability

/-!
# Consistency of standardization over a target covariate law

An outcome model `h θ t x` of arm `t` is fitted in a randomized trial with individual data; the
fitted surface `h θ̂ t` is averaged over the covariate law `Q_X` of a target population. This
file proves that the standardized fitted means, the marginal estimand on a link scale, and the
unanchored and anchored comparisons converge in probability to the corresponding target
quantities, for any fitted parameter `θ̂` that converges in probability. The least squares and
the maximum likelihood fits supply that convergence (`StandardizationConsistencyLeastSquares`,
`OutcomeModelFitLikelihood`); this file is the part shared by all fits.

**What is assumed about the data generating law.**

* The trial is randomized (`Trial.IsRandomizedTwoArm`): measurable covariates, assignment and
  potential outcomes, the assignment independent of the covariates and the potential outcomes,
  `0 < P(A = true) < 1`; the potential outcomes are integrable.
* The outcome model is correct: `h θ₀` is a version of the observed regression `E[Y | X, A]`
  (`PointTreatment.IsOutcomeRegression`). Under randomization `h θ₀ t` is then a conditional
  mean function of `Y(t)` in the trial (`Trial.IsRandomizedTwoArm.isCondMean`).
* Transport: absolute constancy of each arm used from the trial to the target
  (`Transport.StructurallyInvariant`) and overlap `Q_X ≪ T_X`; the target potential outcomes
  are integrable. Then the standardized true surface is the target arm mean
  (`integral_covLaw_eq_armMean_of_trial`).
* Regularity of the model in the parameter near `θ₀` under `Q_X`: almost everywhere
  measurability, an integrable envelope, and continuity in the parameter at `θ₀`.

**Results.** Dominated convergence makes `θ ↦ ∫ h θ t dQ_X` continuous at `θ₀`
(`tendstoInMeasure_integral_of_dominated`), and the fitted surface is `Q_X` integrable with
probability tending to one (`withProbTendingToOne_integrable_of_dominated`), so the limits do not
rest on the value given to the integral of a non integrable function. Then:

* the standardized fitted arm mean converges to the target arm mean
  (`tendstoInMeasure_integral_fit_armMean`);
* the fitted marginal estimand `linkMarginal g Q_X (h θ̂ t₀) (h θ̂ t₁)` converges to the target
  marginal effect (`tendstoInMeasure_linkMarginal_fit`);
* **unanchored comparison** (`tendstoInMeasure_unanchored_fit`): with a reported mean of the
  other treatment in the target, assumed to converge to its target arm mean (as the arm summary
  of a randomized trial of that treatment in the target population does), `g(m̂_b) - g(∫ h θ̂ dQ_X)`
  converges to the target marginal effect;
* **anchored comparison** (`tendstoInMeasure_anchored_fit`): with the reported contrast of the
  common comparator against the other treatment, assumed to converge to its target marginal
  effect, the anchored estimator `linkMarginal g Q_X (h θ̂ t_a) (h θ̂ t_c) - d̂_bc` converges to
  the target marginal effect of `b` relative to `a`.

## Main definitions

* `Trial.IsRandomizedTwoArm`: the randomized two arm trial.

## Main results

* `tendstoInMeasure_integral_of_dominated`, `withProbTendingToOne_integrable_of_dominated`.
* `Trial.IsRandomizedTwoArm.isCondMean`, `integral_covLaw_eq_armMean_of_trial`.
* `tendstoInMeasure_integral_fit_armMean`, `tendstoInMeasure_linkMarginal_fit`,
  `tendstoInMeasure_unanchored_fit`, `tendstoInMeasure_anchored_fit`.

## References

* J. J. Caro and K. J. Ishak, *No head-to-head trial? Simulate the missing arms*,
  PharmacoEconomics 28 (2010).
* D. M. Phillippo, A. E. Ades, S. Dias, S. Palmer, K. R. Abrams and N. J. Welton, *Methods for
  population-adjusted indirect comparisons in health technology appraisal*, Medical Decision
  Making 38 (2018).
-/

@[expose] public section

namespace CausalInference

namespace PopulationAdjustment

open MeasureTheory ProbabilityTheory Filter Topology EffectMeasure IndirectComparison
  PointTreatment Transport

/-! ### Dominated convergence along a consistent parameter -/

section Dominated

variable {𝒳 Ξ Θ : Type*} [MeasurableSpace 𝒳] [MeasurableSpace Ξ] [PseudoMetricSpace Θ]
  {P : Measure Ξ} {ν : Measure 𝒳} {h : Θ → 𝒳 → ℝ} {θ₀ : Θ} {θh : ℕ → Ξ → Θ}

/-- **The standardized fitted surface converges.** If `θ̂ → θ₀` in probability and, near `θ₀`,
the surfaces `h θ` are almost everywhere measurable and bounded by an integrable envelope, and
`θ ↦ h θ x` is continuous at `θ₀` for almost every `x`, then `∫ h θ̂ dν → ∫ h θ₀ dν` in
probability. Dominated convergence and continuous mapping. -/
theorem tendstoInMeasure_integral_of_dominated
    (hmeas : ∀ᶠ θ in 𝓝 θ₀, AEStronglyMeasurable (h θ) ν) {H : 𝒳 → ℝ} (hH : Integrable H ν)
    (hdom : ∀ᶠ θ in 𝓝 θ₀, ∀ᵐ x ∂ν, |h θ x| ≤ H x)
    (hcont : ∀ᵐ x ∂ν, ContinuousAt (fun θ => h θ x) θ₀)
    (hθ : TendstoInMeasure P θh atTop fun _ => θ₀) :
    TendstoInMeasure P (fun n ω => ∫ x, h (θh n ω) x ∂ν) atTop (fun _ => ∫ x, h θ₀ x ∂ν) :=
  hθ.comp_continuousAt (g := fun θ => ∫ x, h θ x ∂ν)
    (continuousAt_of_dominated hmeas (by simpa only [Real.norm_eq_abs] using hdom) hH hcont)

/-- **The fitted surface is integrable with probability tending to one**, under the
measurability and envelope conditions of `tendstoInMeasure_integral_of_dominated`: the
standardized fitted mean is then a genuine integral. -/
theorem withProbTendingToOne_integrable_of_dominated
    (hmeas : ∀ᶠ θ in 𝓝 θ₀, AEStronglyMeasurable (h θ) ν) {H : 𝒳 → ℝ} (hH : Integrable H ν)
    (hdom : ∀ᶠ θ in 𝓝 θ₀, ∀ᵐ x ∂ν, |h θ x| ≤ H x)
    (hθ : TendstoInMeasure P θh atTop fun _ => θ₀) :
    WithProbTendingToOne P (fun n => {ω | Integrable (h (θh n ω)) ν}) := by
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.1 (hmeas.and hdom)
  refine (hθ.withProbTendingToOne_dist_lt hε).mono fun n ω hω => ?_
  obtain ⟨hm, hd⟩ := hball hω
  exact hH.mono' hm (hd.mono fun x hx => by rwa [Real.norm_eq_abs])

end Dominated

/-! ### The randomized trial and the transported surface -/

section Trial

variable {Ω₁ Ω₂ 𝒳 ι : Type*} [MeasurableSpace Ω₁] [MeasurableSpace Ω₂] [MeasurableSpace 𝒳]

/-- A **randomized two arm trial**: measurable covariates, assignment and potential outcomes,
the assignment independent of the covariates and the potential outcomes, and both arms of
positive probability. -/
structure _root_.CausalInference.IndirectComparison.Trial.IsRandomizedTwoArm
    (T : Trial Ω₁ 𝒳 Bool) : Prop where
  /-- The covariates are measurable. -/
  measurable_X : Measurable T.X
  /-- The assignment is measurable. -/
  measurable_A : Measurable T.A
  /-- The potential outcomes are measurable. -/
  measurable_Y : ∀ t, Measurable (T.Y t)
  /-- The assignment is independent of the covariates and the potential outcomes. -/
  indepFun : IndepFun T.A (fun ω => (T.X ω, potentialPair T.Y ω)) T.μ
  /-- The active arm has positive probability. -/
  prob_pos : 0 < T.μ.real (T.A ⁻¹' {true})
  /-- The reference arm has positive probability. -/
  prob_lt_one : T.μ.real (T.A ⁻¹' {true}) < 1

/-- **A correct observed regression of a randomized trial gives conditional mean functions**:
if `m` is a version of `E[Y | X, A]` and the potential outcomes are integrable, `m t` is a
conditional mean function of `Y(t)` in the trial population. -/
theorem _root_.CausalInference.IndirectComparison.Trial.IsRandomizedTwoArm.isCondMean
    {T : Trial Ω₁ 𝒳 Bool} [IsFiniteMeasure T.μ] (hT : T.IsRandomizedTwoArm)
    (hYi : ∀ t, Integrable (T.Y t) T.μ) {m : Bool → 𝒳 → ℝ}
    (hreg : IsOutcomeRegression T.μ T.A T.X T.obsOutcome m) (t : Bool) :
    T.IsCondMean t (m t) :=
  (T.isCondMean_of_indepFun hT.measurable_X hT.measurable_A hT.measurable_Y hYi hT.indepFun
    hT.prob_pos hT.prob_lt_one hreg id).1 t

/-- **Arm identification from a trial arm.** If `f` is a conditional mean function of `Y(t)` in
the trial, the conditional mean of `Y(t)` in the trial and that of `Y(s)` in the target are
given by one function (absolute constancy), and `Q_X ≪ T_X`, then `f` is `Q_X` integrable and
`∫ f dQ_X` is the target mean of `Y(s)`. The trial arm `t` and the target treatment `s` may live
in different index types. -/
theorem integral_covLaw_eq_armMean_of_trial {T : Trial Ω₁ 𝒳 Bool} {Q : Population Ω₂ 𝒳 ι}
    [IsFiniteMeasure Q.μ] {t : Bool} {s : ι} {f : 𝒳 → ℝ} (hX₁ : Measurable T.X)
    (hX₂ : Measurable Q.X) (hYQ : Integrable (Q.Y s) Q.μ) (hf : T.IsCondMean t f)
    (hsi : StructurallyInvariant T.μ T.X (T.Y t) Q.μ Q.X (Q.Y s)) (hov : Q.covLaw ≪ T.covLaw) :
    Integrable f Q.covLaw ∧ ∫ x, f x ∂Q.covLaw = Q.armMean s := by
  have hQ : Q.IsCondMean s f :=
    Population.IsCondMean.of_structurallyInvariant (P := ⟨T.μ, T.X, fun _ => T.Y t⟩) (t := s)
      hX₁ hX₂ hf hsi hov
  exact ⟨hQ.integrable hX₂, hQ.integral_eq hX₂ hYQ⟩

end Trial

/-! ### Consistency of the standardized fitted surface -/

section Consistency

variable {Ω₁ Ω₂ Ξ 𝒳 ι Θ : Type*} [MeasurableSpace Ω₁] [MeasurableSpace Ω₂] [MeasurableSpace Ξ]
  [MeasurableSpace 𝒳] [PseudoMetricSpace Θ] {T : Trial Ω₁ 𝒳 Bool} {Q : Population Ω₂ 𝒳 ι}
  {P : Measure Ξ} {h : Θ → Bool → 𝒳 → ℝ} {θ₀ : Θ} {θh : ℕ → Ξ → Θ}

/-- **The standardized fitted arm mean is consistent for the target arm mean.** In a randomized
trial (`Trial.IsRandomizedTwoArm`) with integrable potential outcomes and a correct outcome model
(`h θ₀` a version of `E[Y | X, A]`), with absolute constancy of arm `t` of the trial and
treatment `s` of the target, overlap and an integrable target outcome, and with the model regular
near `θ₀` under `Q_X` (measurable, an integrable envelope, continuous in the parameter), every
fitted parameter `θ̂ → θ₀` in probability gives `∫ h θ̂ t dQ_X → E_Q[Y(s)]` in probability. -/
theorem tendstoInMeasure_integral_fit_armMean [IsProbabilityMeasure T.μ] [IsFiniteMeasure Q.μ]
    (hT : T.IsRandomizedTwoArm) (hYi : ∀ t, Integrable (T.Y t) T.μ)
    (hreg : IsOutcomeRegression T.μ T.A T.X T.obsOutcome (h θ₀)) (hX₂ : Measurable Q.X)
    {t : Bool} {s : ι} (hYQ : Integrable (Q.Y s) Q.μ)
    (hsi : StructurallyInvariant T.μ T.X (T.Y t) Q.μ Q.X (Q.Y s)) (hov : Q.covLaw ≪ T.covLaw)
    (hmeas : ∀ᶠ θ in 𝓝 θ₀, AEStronglyMeasurable (h θ t) Q.covLaw) {H : 𝒳 → ℝ}
    (hH : Integrable H Q.covLaw) (hdom : ∀ᶠ θ in 𝓝 θ₀, ∀ᵐ x ∂Q.covLaw, |h θ t x| ≤ H x)
    (hcont : ∀ᵐ x ∂Q.covLaw, ContinuousAt (fun θ => h θ t x) θ₀)
    (hθ : TendstoInMeasure P θh atTop fun _ => θ₀) :
    TendstoInMeasure P (fun n ω => ∫ x, h (θh n ω) t x ∂Q.covLaw) atTop
      (fun _ => Q.armMean s) := by
  obtain ⟨-, hval⟩ := integral_covLaw_eq_armMean_of_trial hT.measurable_X hX₂ hYQ
    (hT.isCondMean hYi hreg t) hsi hov
  rw [← hval]
  exact tendstoInMeasure_integral_of_dominated (h := fun θ => h θ t) hmeas hH hdom hcont hθ

/-- **The fitted marginal estimand is consistent for the target marginal effect.** Under the
hypotheses of `tendstoInMeasure_integral_fit_armMean` for the two arms `t₀ ↦ s₀`, `t₁ ↦ s₁`, and
a link `g` continuous at the two target arm means, the marginal estimand of the fitted surfaces
under `Q_X` converges in probability to `g(E_Q[Y(s₁)]) - g(E_Q[Y(s₀)])`. -/
theorem tendstoInMeasure_linkMarginal_fit [IsProbabilityMeasure T.μ] [IsFiniteMeasure Q.μ]
    (hT : T.IsRandomizedTwoArm) (hYi : ∀ t, Integrable (T.Y t) T.μ)
    (hreg : IsOutcomeRegression T.μ T.A T.X T.obsOutcome (h θ₀)) (hX₂ : Measurable Q.X)
    {t₀ t₁ : Bool} {s₀ s₁ : ι} (hYQ₀ : Integrable (Q.Y s₀) Q.μ) (hYQ₁ : Integrable (Q.Y s₁) Q.μ)
    (hsi₀ : StructurallyInvariant T.μ T.X (T.Y t₀) Q.μ Q.X (Q.Y s₀))
    (hsi₁ : StructurallyInvariant T.μ T.X (T.Y t₁) Q.μ Q.X (Q.Y s₁)) (hov : Q.covLaw ≪ T.covLaw)
    (hmeas : ∀ t, ∀ᶠ θ in 𝓝 θ₀, AEStronglyMeasurable (h θ t) Q.covLaw) {H : Bool → 𝒳 → ℝ}
    (hH : ∀ t, Integrable (H t) Q.covLaw)
    (hdom : ∀ t, ∀ᶠ θ in 𝓝 θ₀, ∀ᵐ x ∂Q.covLaw, |h θ t x| ≤ H t x)
    (hcont : ∀ t, ∀ᵐ x ∂Q.covLaw, ContinuousAt (fun θ => h θ t x) θ₀)
    (hθ : TendstoInMeasure P θh atTop fun _ => θ₀) {g : ℝ → ℝ}
    (hg₀ : ContinuousAt g (Q.armMean s₀)) (hg₁ : ContinuousAt g (Q.armMean s₁)) :
    TendstoInMeasure P (fun n ω => linkMarginal g Q.covLaw (h (θh n ω) t₀) (h (θh n ω) t₁))
      atTop (fun _ => Q.marginalEffect g s₀ s₁) := by
  have h₀ := tendstoInMeasure_integral_fit_armMean hT hYi hreg hX₂ hYQ₀ hsi₀ hov (hmeas t₀)
    (hH t₀) (hdom t₀) (hcont t₀) hθ
  have h₁ := tendstoInMeasure_integral_fit_armMean hT hYi hreg hX₂ hYQ₁ hsi₁ hov (hmeas t₁)
    (hH t₁) (hdom t₁) (hcont t₁) hθ
  exact (h₁.comp_continuousAt hg₁).sub (h₀.comp_continuousAt hg₀)

/-- **The unanchored comparison is consistent.** Arm `t` of the trial is standardized to the
target, where it stands for treatment `a`, under the hypotheses of
`tendstoInMeasure_integral_fit_armMean`. The mean outcome `m̂_b` of treatment `b` is reported for
the target (in the application, the target is the population of a trial of `b` and `m̂_b` its
arm summary); it is assumed to converge in probability to `E_Q[Y(b)]`. For a link `g` continuous
at both target arm means, `g(m̂_b) - g(∫ h θ̂ t dQ_X)` converges in probability to the target
marginal effect of `b` relative to `a`. -/
theorem tendstoInMeasure_unanchored_fit [IsProbabilityMeasure T.μ] [IsFiniteMeasure Q.μ]
    (hT : T.IsRandomizedTwoArm) (hYi : ∀ t, Integrable (T.Y t) T.μ)
    (hreg : IsOutcomeRegression T.μ T.A T.X T.obsOutcome (h θ₀)) (hX₂ : Measurable Q.X)
    {t : Bool} {a b : ι} (hYQ : Integrable (Q.Y a) Q.μ)
    (hsi : StructurallyInvariant T.μ T.X (T.Y t) Q.μ Q.X (Q.Y a)) (hov : Q.covLaw ≪ T.covLaw)
    (hmeas : ∀ᶠ θ in 𝓝 θ₀, AEStronglyMeasurable (h θ t) Q.covLaw) {H : 𝒳 → ℝ}
    (hH : Integrable H Q.covLaw) (hdom : ∀ᶠ θ in 𝓝 θ₀, ∀ᵐ x ∂Q.covLaw, |h θ t x| ≤ H x)
    (hcont : ∀ᵐ x ∂Q.covLaw, ContinuousAt (fun θ => h θ t x) θ₀)
    (hθ : TendstoInMeasure P θh atTop fun _ => θ₀) {mb : ℕ → Ξ → ℝ}
    (hmb : TendstoInMeasure P mb atTop fun _ => Q.armMean b) {g : ℝ → ℝ}
    (hga : ContinuousAt g (Q.armMean a)) (hgb : ContinuousAt g (Q.armMean b)) :
    TendstoInMeasure P (fun n ω => g (mb n ω) - g (∫ x, h (θh n ω) t x ∂Q.covLaw)) atTop
      (fun _ => Q.marginalEffect g a b) :=
  (hmb.comp_continuousAt hgb).sub
    ((tendstoInMeasure_integral_fit_armMean hT hYi hreg hX₂ hYQ hsi hov hmeas hH hdom hcont
      hθ).comp_continuousAt hga)

/-- **The anchored comparison is consistent.** The trial compares the common comparator `c`
(arm `t_c`) with `a` (arm `t_a`); both arms are standardized to the target under the hypotheses
of `tendstoInMeasure_integral_fit_armMean`. The contrast `d̂_bc` of `c` relative to `b` is
reported (in the application, the aggregate contrast of a trial of `b` against `c`); it is
assumed to converge in probability to the target marginal effect of `c` relative to `b`. For a
link `g` continuous at the target means of `a` and `c`, the anchored estimator
`linkMarginal g Q_X (h θ̂ t_a) (h θ̂ t_c) - d̂_bc` converges in probability to the target
marginal effect of `b` relative to `a`. -/
theorem tendstoInMeasure_anchored_fit [IsProbabilityMeasure T.μ] [IsFiniteMeasure Q.μ]
    (hT : T.IsRandomizedTwoArm) (hYi : ∀ t, Integrable (T.Y t) T.μ)
    (hreg : IsOutcomeRegression T.μ T.A T.X T.obsOutcome (h θ₀)) (hX₂ : Measurable Q.X)
    {ta tc : Bool} {a b c : ι} (hYQa : Integrable (Q.Y a) Q.μ) (hYQc : Integrable (Q.Y c) Q.μ)
    (hsia : StructurallyInvariant T.μ T.X (T.Y ta) Q.μ Q.X (Q.Y a))
    (hsic : StructurallyInvariant T.μ T.X (T.Y tc) Q.μ Q.X (Q.Y c)) (hov : Q.covLaw ≪ T.covLaw)
    (hmeas : ∀ t, ∀ᶠ θ in 𝓝 θ₀, AEStronglyMeasurable (h θ t) Q.covLaw) {H : Bool → 𝒳 → ℝ}
    (hH : ∀ t, Integrable (H t) Q.covLaw)
    (hdom : ∀ t, ∀ᶠ θ in 𝓝 θ₀, ∀ᵐ x ∂Q.covLaw, |h θ t x| ≤ H t x)
    (hcont : ∀ t, ∀ᵐ x ∂Q.covLaw, ContinuousAt (fun θ => h θ t x) θ₀)
    (hθ : TendstoInMeasure P θh atTop fun _ => θ₀) {dbc : ℕ → Ξ → ℝ} {g : ℝ → ℝ}
    (hdbc : TendstoInMeasure P dbc atTop fun _ => Q.marginalEffect g b c)
    (hga : ContinuousAt g (Q.armMean a)) (hgc : ContinuousAt g (Q.armMean c)) :
    TendstoInMeasure P
      (fun n ω => linkMarginal g Q.covLaw (h (θh n ω) ta) (h (θh n ω) tc) - dbc n ω) atTop
      (fun _ => Q.marginalEffect g a b) := by
  have hac := tendstoInMeasure_linkMarginal_fit hT hYi hreg hX₂ hYQa hYQc hsia hsic hov hmeas hH
    hdom hcont hθ hga hgc
  have e : Q.marginalEffect g a c - Q.marginalEffect g b c = Q.marginalEffect g a b := by
    simp only [Population.marginalEffect]; ring
  rw [← e]
  exact hac.sub hdbc

end Consistency

end PopulationAdjustment

end CausalInference
