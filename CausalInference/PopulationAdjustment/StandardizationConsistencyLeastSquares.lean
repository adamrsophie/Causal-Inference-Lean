/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.PopulationAdjustment.StandardizationConsistencyMarginal
public import CausalInference.PopulationAdjustment.OutcomeModelFitLeastSquares

/-!
# Standardization of a least squares outcome model: consistency from the model

A linear outcome model `E[Y | X, A] = z(A, X)ᵀξ₀` is fitted by least squares to the individual
data of a randomized trial and standardized to the covariate law `Q_X` of a target. The
assumptions on the trial are collected in `Trial.LinearOutcomeModel`: measurable design
coordinates with finite second moments, potential outcomes with finite second moments, a
positive definite design second moment, and a correct linear regression. From these and
randomization alone the fitted coefficient converges
(`Trial.LinearOutcomeModel.tendstoInMeasure`), and the fitted surface `x ↦ z(t, x)ᵀξ` is
regular in the parameter under any target law with integrable design rows
(`linearSurface_dominated`). No convergence, measurability or invertibility premise is left in
the final theorems:

* `tendstoInMeasure_leastSquares_armMean`: the standardized fitted arm mean converges to the
  target arm mean;
* `tendstoInMeasure_leastSquares_linkMarginal`: the fitted marginal estimand converges to the
  target marginal effect on a link continuous at the target arm means;
* `tendstoInMeasure_leastSquares_unanchored`, `tendstoInMeasure_leastSquares_anchored`: the
  unanchored and anchored comparisons with a reported mean or a reported contrast.

The standardized fitted mean is `(∫ z(t, x) dQ_X) ⬝ ξ̂` (`integral_dotProduct_eq`): a function
of the trial data and of the target means of the design row only.

## Main definitions

* `Trial.LinearOutcomeModel`: the assumptions on a trial with a linear outcome model.

## Main results

* `memLp_two_select`, `linearSurface_dominated`, `integral_dotProduct_eq`.
* `Trial.LinearOutcomeModel.tendstoInMeasure`.
* `tendstoInMeasure_leastSquares_armMean`, `tendstoInMeasure_leastSquares_linkMarginal`,
  `tendstoInMeasure_leastSquares_unanchored`, `tendstoInMeasure_leastSquares_anchored`.

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

open MeasureTheory ProbabilityTheory Filter Topology Matrix EffectMeasure IndirectComparison
  PointTreatment Transport

/-! ### Moments and regularity of the linear surface -/

section Linear

variable {Ω 𝒳 κ : Type*} [MeasurableSpace Ω] [MeasurableSpace 𝒳] [Fintype κ]

/-- **The variable of the assigned arm has finite second moments** when the variable of each arm
has: for measurable `f t` with `f t ∈ L²` and a measurable assignment `A`,
`ω ↦ f (A ω) ω ∈ L²`. -/
theorem memLp_two_select {μ : Measure Ω} {A : Ω → Bool} (hA : Measurable A) {f : Bool → Ω → ℝ}
    (hf : ∀ t, Measurable (f t)) (hf2 : ∀ t, MemLp (f t) 2 μ) :
    MemLp (fun ω => f (A ω) ω) 2 μ := by
  have hm : Measurable fun ω => f (A ω) ω :=
    (measurable_from_prod_countable_left (f := fun q : Ω × Bool => f q.2 q.1)
      fun t => hf t).comp (measurable_id.prodMk hA)
  refine ((hf2 true).norm.add (hf2 false).norm).of_le hm.aestronglyMeasurable
    (Eventually.of_forall fun ω => ?_)
  have h0 : 0 ≤ ‖f true ω‖ + ‖f false ω‖ := by positivity
  simp only [Pi.add_apply, Real.norm_of_nonneg h0]
  cases A ω
  · exact le_add_of_nonneg_left (norm_nonneg _)
  · exact le_add_of_nonneg_right (norm_nonneg _)

/-- **The linear surface is regular in the coefficient.** For a design row `z` with measurable
coordinates that are integrable under `ν`, the surfaces `x ↦ z(x) ⬝ ξ` are measurable, bounded
near `ξ₀` by the integrable envelope `(‖ξ₀‖ + 1) ∑ⱼ |z(x)ⱼ|`, and continuous in `ξ`. -/
theorem linearSurface_dominated {z : 𝒳 → κ → ℝ} (hz : ∀ j, Measurable fun x => z x j)
    {ν : Measure 𝒳} (hzi : ∀ j, Integrable (fun x => z x j) ν) (ξ₀ : κ → ℝ) :
    (∀ ξ : κ → ℝ, AEStronglyMeasurable (fun x => z x ⬝ᵥ ξ) ν) ∧
      Integrable (fun x => (‖ξ₀‖ + 1) * ∑ j, |z x j|) ν ∧
      (∀ᶠ ξ in 𝓝 ξ₀, ∀ᵐ x ∂ν, |z x ⬝ᵥ ξ| ≤ (‖ξ₀‖ + 1) * ∑ j, |z x j|) ∧
      ∀ᵐ x ∂ν, ContinuousAt (fun ξ => z x ⬝ᵥ ξ) ξ₀ := by
  refine ⟨fun ξ => (Finset.measurable_sum _ fun j _ => (hz j).mul_const _).aestronglyMeasurable,
    (integrable_finsetSum _ fun j _ => (hzi j).abs).const_mul _, ?_,
    ae_of_all _ fun x => (continuous_const.dotProduct continuous_id).continuousAt⟩
  filter_upwards [Metric.ball_mem_nhds ξ₀ one_pos] with ξ hξ
  refine ae_of_all _ fun x => ?_
  have hn : ‖ξ‖ ≤ ‖ξ₀‖ + 1 := by
    have h1 := norm_sub_norm_le ξ ξ₀
    rw [Metric.mem_ball, dist_eq_norm] at hξ
    linarith
  have hdot : |z x ⬝ᵥ ξ| ≤ ‖ξ‖ * ∑ j, |z x j| := by
    rw [dotProduct, Finset.mul_sum]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => ?_)
    rw [abs_mul, mul_comm]
    exact mul_le_mul_of_nonneg_right (by simpa using norm_le_pi_norm ξ j) (abs_nonneg _)
  exact hdot.trans (mul_le_mul_of_nonneg_right hn (Finset.sum_nonneg fun j _ => abs_nonneg _))

/-- **The standardized linear surface is the dot product of the target design means with the
coefficient**: `∫ z(x) ⬝ ξ dν = (∫ z dν) ⬝ ξ`, for integrable design coordinates. -/
theorem integral_dotProduct_eq {z : 𝒳 → κ → ℝ} {ν : Measure 𝒳}
    (hzi : ∀ j, Integrable (fun x => z x j) ν) (ξ : κ → ℝ) :
    ∫ x, z x ⬝ᵥ ξ ∂ν = (fun j => ∫ x, z x j ∂ν) ⬝ᵥ ξ := by
  simp only [dotProduct]
  rw [integral_finsetSum _ fun j _ => (hzi j).mul_const _]
  simp only [integral_mul_const]

end Linear

/-! ### The trial with a linear outcome model -/

section Model

variable {Ω₁ Ω₂ Ξ 𝒳 ι κ : Type*} [MeasurableSpace Ω₁] [MeasurableSpace Ω₂] [MeasurableSpace Ξ]
  [MeasurableSpace 𝒳] [Fintype κ] [DecidableEq κ]

/-- The **assumptions on a trial with a linear outcome model** `z(a, x)ᵀξ₀`: measurable design
coordinates, design coordinates and potential outcomes with finite second moments, a positive
definite design second moment `E[z(A, X) z(A, X)ᵀ]`, and a correct linear regression
`E[Y | X, A] = z(A, X)ᵀξ₀`. -/
structure _root_.CausalInference.IndirectComparison.Trial.LinearOutcomeModel
    (T : Trial Ω₁ 𝒳 Bool) (z : Bool → 𝒳 → κ → ℝ) (ξ₀ : κ → ℝ) : Prop where
  /-- The design coordinates are measurable. -/
  measurable_z : ∀ a j, Measurable fun x => z a x j
  /-- The design coordinates of each arm have finite second moments in the trial. -/
  memLp_z : ∀ a j, MemLp (fun ω => z a (T.X ω) j) 2 T.μ
  /-- The potential outcomes have finite second moments in the trial. -/
  memLp_Y : ∀ t, MemLp (T.Y t) 2 T.μ
  /-- The design second moment is positive definite. -/
  posDef : (Matrix.of fun j k => ∫ ω, z (T.A ω) (T.X ω) j * z (T.A ω) (T.X ω) k ∂T.μ).PosDef
  /-- The linear surface is a version of the observed regression `E[Y | X, A]`. -/
  isOutcomeRegression : IsOutcomeRegression T.μ T.A T.X T.obsOutcome fun a x => z a x ⬝ᵥ ξ₀

variable {T : Trial Ω₁ 𝒳 Bool} {z : Bool → 𝒳 → κ → ℝ} {ξ₀ : κ → ℝ}

omit [DecidableEq κ] in
/-- The potential outcomes of a linear outcome model are integrable. -/
theorem _root_.CausalInference.IndirectComparison.Trial.LinearOutcomeModel.integrable_Y
    [IsFiniteMeasure T.μ] (hM : T.LinearOutcomeModel z ξ₀) (t : Bool) :
    Integrable (T.Y t) T.μ :=
  (hM.memLp_Y t).integrable one_le_two

/-- **The least squares fit of a linear outcome model is consistent.** In a randomized trial
with a linear outcome model, for an i.i.d. sample of individual records with the law
`Trial.ipdLaw` of the trial, the least squares fit converges in probability to `ξ₀`; the sample
design is invertible with probability tending to one (`withProbTendingToOne_det_fitGram_ne_zero`)
and the fit is then the least squares solution. -/
theorem _root_.CausalInference.IndirectComparison.Trial.LinearOutcomeModel.tendstoInMeasure
    [IsProbabilityMeasure T.μ] {P : Measure Ξ} [IsProbabilityMeasure P]
    (hM : T.LinearOutcomeModel z ξ₀) (hT : T.IsRandomizedTwoArm) {O : ℕ → Ξ → 𝒳 × Bool × ℝ}
    (hO : IsIIDSample O P) (hlaw : P.map (O 0) = T.ipdLaw) :
    TendstoInMeasure P (leastSquaresFit (recordDesign z) recordResponse O) atTop
      (fun _ => ξ₀) := by
  have hYo : Measurable T.obsOutcome :=
    measurable_obsOutcome (A := T.A) (Y := T.Y) hT.measurable_A hT.measurable_Y
  refine tendstoInMeasure_leastSquaresFit_of_isOutcomeRegression hT.measurable_X
    hT.measurable_A hYo hM.measurable_z (fun j => ?_)
    (memLp_two_select hT.measurable_A hT.measurable_Y hM.memLp_Y) hM.isOutcomeRegression
    hM.posDef hO hlaw
  exact memLp_two_select (f := fun a ω => z a (T.X ω) j) hT.measurable_A
    (fun a => (hM.measurable_z a j).comp hT.measurable_X) fun a => hM.memLp_z a j

variable {Q : Population Ω₂ 𝒳 ι} {P : Measure Ξ} {O : ℕ → Ξ → 𝒳 × Bool × ℝ}

/-- **Standardization of the least squares fit is consistent for the target arm mean.** In a
randomized trial with a linear outcome model (`Trial.LinearOutcomeModel`) and an i.i.d. sample of
its individual records, with absolute constancy of arm `t` of the trial and treatment `s` of the
target, overlap `Q_X ≪ T_X`, an integrable target outcome and design coordinates of arm `t`
integrable under `Q_X`, the standardized fitted mean `∫ z(t, x)ᵀξ̂ dQ_X` converges in
probability to `E_Q[Y(s)]`. -/
theorem tendstoInMeasure_leastSquares_armMean [IsProbabilityMeasure T.μ] [IsFiniteMeasure Q.μ]
    [IsProbabilityMeasure P] (hT : T.IsRandomizedTwoArm) (hM : T.LinearOutcomeModel z ξ₀)
    (hO : IsIIDSample O P) (hlaw : P.map (O 0) = T.ipdLaw) (hX₂ : Measurable Q.X) {t : Bool}
    {s : ι} (hYQ : Integrable (Q.Y s) Q.μ)
    (hsi : StructurallyInvariant T.μ T.X (T.Y t) Q.μ Q.X (Q.Y s)) (hov : Q.covLaw ≪ T.covLaw)
    (hzQ : ∀ j, Integrable (fun x => z t x j) Q.covLaw) :
    TendstoInMeasure P
      (fun n ω => ∫ x, z t x ⬝ᵥ leastSquaresFit (recordDesign z) recordResponse O n ω
        ∂Q.covLaw) atTop (fun _ => Q.armMean s) := by
  obtain ⟨hm, hH, hdom, hcont⟩ := linearSurface_dominated (hM.measurable_z t) hzQ ξ₀
  exact tendstoInMeasure_integral_fit_armMean (h := fun ξ a x => z a x ⬝ᵥ ξ) hT hM.integrable_Y
    hM.isOutcomeRegression hX₂ hYQ hsi hov (Eventually.of_forall hm) hH hdom hcont
    (hM.tendstoInMeasure hT hO hlaw)

/-- **The standardized least squares marginal estimand is consistent for the target marginal
effect.** Under the hypotheses of `tendstoInMeasure_leastSquares_armMean` for the two arms
`t₀ ↦ s₀`, `t₁ ↦ s₁`, and a link `g` continuous at the two target arm means,
`linkMarginal g Q_X (z(t₀, ·)ᵀξ̂) (z(t₁, ·)ᵀξ̂)` converges in probability to
`g(E_Q[Y(s₁)]) - g(E_Q[Y(s₀)])`. -/
theorem tendstoInMeasure_leastSquares_linkMarginal [IsProbabilityMeasure T.μ]
    [IsFiniteMeasure Q.μ] [IsProbabilityMeasure P] (hT : T.IsRandomizedTwoArm)
    (hM : T.LinearOutcomeModel z ξ₀) (hO : IsIIDSample O P) (hlaw : P.map (O 0) = T.ipdLaw)
    (hX₂ : Measurable Q.X) {t₀ t₁ : Bool} {s₀ s₁ : ι} (hYQ₀ : Integrable (Q.Y s₀) Q.μ)
    (hYQ₁ : Integrable (Q.Y s₁) Q.μ)
    (hsi₀ : StructurallyInvariant T.μ T.X (T.Y t₀) Q.μ Q.X (Q.Y s₀))
    (hsi₁ : StructurallyInvariant T.μ T.X (T.Y t₁) Q.μ Q.X (Q.Y s₁)) (hov : Q.covLaw ≪ T.covLaw)
    (hzQ : ∀ t j, Integrable (fun x => z t x j) Q.covLaw) {g : ℝ → ℝ}
    (hg₀ : ContinuousAt g (Q.armMean s₀)) (hg₁ : ContinuousAt g (Q.armMean s₁)) :
    TendstoInMeasure P
      (fun n ω => linkMarginal g Q.covLaw
        (fun x => z t₀ x ⬝ᵥ leastSquaresFit (recordDesign z) recordResponse O n ω)
        (fun x => z t₁ x ⬝ᵥ leastSquaresFit (recordDesign z) recordResponse O n ω))
      atTop (fun _ => Q.marginalEffect g s₀ s₁) := by
  have hreg := fun t => linearSurface_dominated (hM.measurable_z t) (hzQ t) ξ₀
  exact tendstoInMeasure_linkMarginal_fit (h := fun ξ a x => z a x ⬝ᵥ ξ) hT hM.integrable_Y
    hM.isOutcomeRegression hX₂ hYQ₀ hYQ₁ hsi₀ hsi₁ hov
    (fun t => Eventually.of_forall (hreg t).1) (fun t => (hreg t).2.1) (fun t => (hreg t).2.2.1)
    (fun t => (hreg t).2.2.2) (hM.tendstoInMeasure hT hO hlaw) hg₀ hg₁

/-- **The unanchored comparison with the least squares fit is consistent.** Under the hypotheses
of `tendstoInMeasure_leastSquares_armMean` for arm `t ↦ a`, with a reported mean `m̂_b` of
treatment `b` in the target converging in probability to `E_Q[Y(b)]` and a link `g` continuous
at both target arm means, `g(m̂_b) - g(∫ z(t, x)ᵀξ̂ dQ_X)` converges in probability to the target
marginal effect of `b` relative to `a`. -/
theorem tendstoInMeasure_leastSquares_unanchored [IsProbabilityMeasure T.μ]
    [IsFiniteMeasure Q.μ] [IsProbabilityMeasure P] (hT : T.IsRandomizedTwoArm)
    (hM : T.LinearOutcomeModel z ξ₀) (hO : IsIIDSample O P) (hlaw : P.map (O 0) = T.ipdLaw)
    (hX₂ : Measurable Q.X) {t : Bool} {a b : ι} (hYQ : Integrable (Q.Y a) Q.μ)
    (hsi : StructurallyInvariant T.μ T.X (T.Y t) Q.μ Q.X (Q.Y a)) (hov : Q.covLaw ≪ T.covLaw)
    (hzQ : ∀ j, Integrable (fun x => z t x j) Q.covLaw) {mb : ℕ → Ξ → ℝ}
    (hmb : TendstoInMeasure P mb atTop fun _ => Q.armMean b) {g : ℝ → ℝ}
    (hga : ContinuousAt g (Q.armMean a)) (hgb : ContinuousAt g (Q.armMean b)) :
    TendstoInMeasure P
      (fun n ω => g (mb n ω) -
        g (∫ x, z t x ⬝ᵥ leastSquaresFit (recordDesign z) recordResponse O n ω ∂Q.covLaw))
      atTop (fun _ => Q.marginalEffect g a b) :=
  (hmb.comp_continuousAt hgb).sub
    ((tendstoInMeasure_leastSquares_armMean hT hM hO hlaw hX₂ hYQ hsi hov
      hzQ).comp_continuousAt hga)

/-- **The anchored comparison with the least squares fit is consistent.** The trial compares the
common comparator `c` (arm `t_c`) with `a` (arm `t_a`), both standardized to the target under the
hypotheses of `tendstoInMeasure_leastSquares_linkMarginal`. With a reported contrast `d̂_bc`
converging in probability to the target marginal effect of `c` relative to `b`, and a link `g`
continuous at the target means of `a` and `c`, the anchored estimator converges in probability
to the target marginal effect of `b` relative to `a`. -/
theorem tendstoInMeasure_leastSquares_anchored [IsProbabilityMeasure T.μ]
    [IsFiniteMeasure Q.μ] [IsProbabilityMeasure P] (hT : T.IsRandomizedTwoArm)
    (hM : T.LinearOutcomeModel z ξ₀) (hO : IsIIDSample O P) (hlaw : P.map (O 0) = T.ipdLaw)
    (hX₂ : Measurable Q.X) {ta tc : Bool} {a b c : ι} (hYQa : Integrable (Q.Y a) Q.μ)
    (hYQc : Integrable (Q.Y c) Q.μ)
    (hsia : StructurallyInvariant T.μ T.X (T.Y ta) Q.μ Q.X (Q.Y a))
    (hsic : StructurallyInvariant T.μ T.X (T.Y tc) Q.μ Q.X (Q.Y c)) (hov : Q.covLaw ≪ T.covLaw)
    (hzQ : ∀ t j, Integrable (fun x => z t x j) Q.covLaw) {dbc : ℕ → Ξ → ℝ} {g : ℝ → ℝ}
    (hdbc : TendstoInMeasure P dbc atTop fun _ => Q.marginalEffect g b c)
    (hga : ContinuousAt g (Q.armMean a)) (hgc : ContinuousAt g (Q.armMean c)) :
    TendstoInMeasure P
      (fun n ω => linkMarginal g Q.covLaw
        (fun x => z ta x ⬝ᵥ leastSquaresFit (recordDesign z) recordResponse O n ω)
        (fun x => z tc x ⬝ᵥ leastSquaresFit (recordDesign z) recordResponse O n ω) - dbc n ω)
      atTop (fun _ => Q.marginalEffect g a b) := by
  have hreg := fun t => linearSurface_dominated (hM.measurable_z t) (hzQ t) ξ₀
  exact tendstoInMeasure_anchored_fit (h := fun ξ a x => z a x ⬝ᵥ ξ) hT hM.integrable_Y
    hM.isOutcomeRegression hX₂ hYQa hYQc hsia hsic hov
    (fun t => Eventually.of_forall (hreg t).1) (fun t => (hreg t).2.1) (fun t => (hreg t).2.2.1)
    (fun t => (hreg t).2.2.2) (hM.tendstoInMeasure hT hO hlaw) hdbc hga hgc

end Model

end PopulationAdjustment

end CausalInference
