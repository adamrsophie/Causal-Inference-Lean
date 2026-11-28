/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.PopulationAdjustment.StandardizationConsistencyTargetSample
public import CausalInference.PopulationAdjustment.OutcomeModelPlugInBias

/-!
# The conditional plug-in with a fitted outcome model

Instead of averaging the fitted surface over the target covariate law, the conditional plug-in
evaluates the fitted link contrast at the target covariate mean `x̄`:
`g(m̂_b(x̄)) - g(m̂_a(x̄))`. For an outcome model whose link transforms the mean into the
predictor with treatment interactions,
`g(m(t, x)) = α + xᵀβ₁ + 1[t](γ + xᵀβ₂)` (`interactionPredictor`), this file writes the model as
a linear predictor in one coefficient vector over the design `interactionDesign`, so that the
coefficient fitted by least squares or by maximum likelihood can be plugged in directly.

**What is assumed about the data generating law.** The trial is randomized
(`Trial.IsRandomizedTwoArm`) with integrable potential outcomes, the outcome model
`ginv(z(t, x)ᵀξ₀)` is a version of `E[Y | X, A]`, and the link `g` is a left inverse of `ginv`
(`g (ginv s) = s`). Each arm used is transported to the target (absolute constancy and overlap),
the target outcomes are integrable and the target covariates have integrable coordinates. The
fitted coefficient converges in probability to `ξ₀`, and the target covariate mean is either
reported as a quantity converging to `x̄` or computed from i.i.d. target draws.

**Results.**

* `tendstoInMeasure_conditionalPlugIn`: the conditional plug-in converges in probability to the
  link contrast of the true model at `x̄`, which is the average conditional effect
  `γ + x̄ᵀβ₂`, and **differs from the target marginal effect by the averaging gap**
  `J_g(m_a) - J_g(m_b)` (`plugInEffect_sub_linkMarginal`). The plug-in is therefore not
  consistent for the marginal effect on a nonlinear link unless the averaging gaps agree.
* `tendstoInMeasure_conditionalPlugIn_sampleMean`: the same with the covariate mean of a target
  sample.
* `tendstoInMeasure_conditionalPlugIn_leastSquares`: on the identity link the averaging gap
  vanishes; the plug-in of the least squares coefficient at the target mean is consistent for
  the target marginal effect.

## Main definitions

* `interactionDesign`: the design row of the interaction predictor.

## Main results

* `interactionDesign_dotProduct`, `tendstoInMeasure_comp_tendsto_atTop`,
  `tendstoInMeasure_sampleMean_coord`.
* `tendstoInMeasure_conditionalPlugIn`, `tendstoInMeasure_conditionalPlugIn_sampleMean`,
  `tendstoInMeasure_conditionalPlugIn_leastSquares`.

## References

* D. M. Phillippo, A. E. Ades, S. Dias, S. Palmer, K. R. Abrams and N. J. Welton, *Methods for
  population-adjusted indirect comparisons in health technology appraisal*, Medical Decision
  Making 38 (2018).
-/

@[expose] public section

namespace CausalInference

namespace PopulationAdjustment

open MeasureTheory ProbabilityTheory Filter Topology Matrix EffectMeasure IndirectComparison
  PointTreatment Transport

/-- **Convergence in probability to a constant along sample sizes tending to infinity.** -/
theorem tendstoInMeasure_comp_tendsto_atTop {Ω E : Type*} [MeasurableSpace Ω] [EDist E]
    {μ : Measure Ω} {f : ℕ → Ω → E} {c : E} (h : TendstoInMeasure μ f atTop fun _ => c)
    {m : ℕ → ℕ} (hm : Tendsto m atTop atTop) :
    TendstoInMeasure μ (fun n => f (m n)) atTop fun _ => c :=
  fun ε hε => (h ε hε).comp hm

/-- **The coordinatewise law of large numbers**: the sample mean vector of an i.i.d. sample of
vectors with integrable coordinates converges in probability to the mean vector. -/
theorem tendstoInMeasure_sampleMean_coord {ι Ξ : Type*} [Fintype ι] [MeasurableSpace Ξ]
    {P : Measure Ξ} [IsProbabilityMeasure P] {Xs : ℕ → Ξ → ι → ℝ} (hXs : IsIIDSample Xs P)
    (hν : ∀ k, Integrable (fun x : ι → ℝ => x k) (P.map (Xs 0))) :
    TendstoInMeasure P (fun n ω k => sampleMean (fun x : ι → ℝ => x k) Xs n ω) atTop
      (fun _ k => ∫ x, x k ∂(P.map (Xs 0))) := by
  refine tendstoInMeasure_pi (X := fun k n ω => sampleMean (fun x : ι → ℝ => x k) Xs n ω)
    fun k => ?_
  have hmk : Measurable fun x : ι → ℝ => x k := measurable_pi_apply k
  have hk := sampleMean_isConsistent hXs hmk
    ((integrable_map_measure hmk.aestronglyMeasurable (hXs.aemeasurable 0)).1 (hν k))
  rw [IsConsistent, ← integral_map (hXs.aemeasurable 0) hmk.aestronglyMeasurable] at hk
  exact hk

/-! ### The interaction predictor as a linear predictor -/

section Design

variable {p : ℕ}

/-- The **design row of the interaction predictor**: the coefficient vector is indexed by
`Option (Fin p) ⊕ Option (Fin p)`, the left part holding the intercept `α` (`none`) and the
main effects `β₁`, the right part the treatment effect `γ` (`none`) and the interactions `β₂`.
The row of arm `t` at `x` is `(1, x, 1[t], 1[t] x)`. -/
def interactionDesign (t : Bool) (x : Fin p → ℝ) : Option (Fin p) ⊕ Option (Fin p) → ℝ
  | .inl none => 1
  | .inl (some j) => x j
  | .inr none => if t then 1 else 0
  | .inr (some j) => if t then x j else 0

/-- The intercept of a coefficient vector of the interaction design. -/
def interactionIntercept (ξ : Option (Fin p) ⊕ Option (Fin p) → ℝ) : ℝ := ξ (.inl none)

/-- The main effects of a coefficient vector of the interaction design. -/
def interactionMain (ξ : Option (Fin p) ⊕ Option (Fin p) → ℝ) : Fin p → ℝ :=
  fun j => ξ (.inl (some j))

/-- The treatment effect of a coefficient vector of the interaction design. -/
def interactionEffect (ξ : Option (Fin p) ⊕ Option (Fin p) → ℝ) : ℝ := ξ (.inr none)

/-- The interactions of a coefficient vector of the interaction design. -/
def interactionModifier (ξ : Option (Fin p) ⊕ Option (Fin p) → ℝ) : Fin p → ℝ :=
  fun j => ξ (.inr (some j))

/-- **The interaction design reproduces the interaction predictor**:
`z(t, x) ⬝ ξ = α + xᵀβ₁ + 1[t](γ + xᵀβ₂)` with the coefficients read off `ξ`. -/
theorem interactionDesign_dotProduct (t : Bool) (x : Fin p → ℝ)
    (ξ : Option (Fin p) ⊕ Option (Fin p) → ℝ) :
    interactionDesign t x ⬝ᵥ ξ = interactionPredictor (interactionIntercept ξ)
      (interactionEffect ξ) (interactionMain ξ) (interactionModifier ξ) t x := by
  cases t <;>
    simp [dotProduct, Fintype.sum_sum_type, Fintype.sum_option, interactionDesign,
      interactionPredictor, interactionIntercept, interactionEffect, interactionMain,
      interactionModifier]

/-- The coordinates of the interaction design are measurable. -/
theorem measurable_interactionDesign (t : Bool) (k : Option (Fin p) ⊕ Option (Fin p)) :
    Measurable fun x : Fin p → ℝ => interactionDesign t x k := by
  rcases k with (_ | j) | (_ | j) <;> cases t <;>
    simp only [interactionDesign, Bool.false_eq_true, ↓reduceIte] <;>
    first | exact measurable_const | exact measurable_pi_apply j

/-- The coordinates of the interaction design are integrable under a probability law with
integrable covariate coordinates. -/
theorem integrable_interactionDesign {ν : Measure (Fin p → ℝ)} [IsProbabilityMeasure ν]
    (hν : ∀ k, Integrable (fun x : Fin p → ℝ => x k) ν) (t : Bool)
    (k : Option (Fin p) ⊕ Option (Fin p)) :
    Integrable (fun x => interactionDesign t x k) ν := by
  rcases k with (_ | j) | (_ | j) <;> cases t <;>
    simp only [interactionDesign, Bool.false_eq_true, ↓reduceIte] <;>
    first | exact integrable_const _ | exact hν j

end Design

/-! ### The limit of the conditional plug-in -/

section Limit

variable {p : ℕ} {Ω₁ Ω₂ Ξ ι : Type*} [MeasurableSpace Ω₁] [MeasurableSpace Ω₂]
  [MeasurableSpace Ξ] {T : Trial Ω₁ (Fin p → ℝ) Bool} {Q : Population Ω₂ (Fin p → ℝ) ι}
  {P : Measure Ξ}

/-- **The conditional plug-in converges, and misses the marginal effect by the averaging gap.**
In a randomized trial with integrable potential outcomes and a correct outcome model
`E[Y | X, A] = ginv(z(A, X)ᵀξ₀)` over the interaction design, with a link `g` satisfying
`g (ginv s) = s`, with both arms transported to the target (`false ↦ s₀`, `true ↦ s₁`),
integrable target outcomes and target covariates with integrable coordinates, let the fitted
coefficient `ξ̂` converge in probability to `ξ₀` and the reported target covariate mean `x̂`
converge in probability to `x̄ = E_Q[X]`. Then the conditional plug-in
`g(ginv(z(true, x̂)ᵀξ̂)) - g(ginv(z(false, x̂)ᵀξ̂))` converges in probability to
`Δ_Q + J_g(m₀) - J_g(m₁)`, where `Δ_Q` is the target marginal effect of `s₁` relative to `s₀`
and `J_g(m_t) = g(∫ m_t dQ_X) - ∫ g ∘ m_t dQ_X` is the averaging gap of the true surface of arm
`t`. -/
theorem tendstoInMeasure_conditionalPlugIn [IsProbabilityMeasure T.μ] [IsProbabilityMeasure Q.μ]
    (hT : T.IsRandomizedTwoArm) (hYi : ∀ t, Integrable (T.Y t) T.μ) {g ginv : ℝ → ℝ}
    (hg : ∀ s, g (ginv s) = s) {ξ₀ : Option (Fin p) ⊕ Option (Fin p) → ℝ}
    (hreg : IsOutcomeRegression T.μ T.A T.X T.obsOutcome
      fun t x => ginv (interactionDesign t x ⬝ᵥ ξ₀))
    (hX₂ : Measurable Q.X) {s₀ s₁ : ι} (hYQ₀ : Integrable (Q.Y s₀) Q.μ)
    (hYQ₁ : Integrable (Q.Y s₁) Q.μ)
    (hsi₀ : StructurallyInvariant T.μ T.X (T.Y false) Q.μ Q.X (Q.Y s₀))
    (hsi₁ : StructurallyInvariant T.μ T.X (T.Y true) Q.μ Q.X (Q.Y s₁))
    (hov : Q.covLaw ≪ T.covLaw) (hν : ∀ k, Integrable (fun x : Fin p → ℝ => x k) Q.covLaw)
    {ξh : ℕ → Ξ → Option (Fin p) ⊕ Option (Fin p) → ℝ}
    (hξ : TendstoInMeasure P ξh atTop fun _ => ξ₀) {xh : ℕ → Ξ → Fin p → ℝ}
    (hx : TendstoInMeasure P xh atTop fun _ => covMean Q.covLaw) :
    TendstoInMeasure P
      (fun n ω => linkContrast g (fun x => ginv (interactionDesign false x ⬝ᵥ ξh n ω))
        (fun x => ginv (interactionDesign true x ⬝ᵥ ξh n ω)) (xh n ω)) atTop
      (fun _ => Q.marginalEffect g s₀ s₁ +
        (averagingGap g Q.covLaw (fun x => ginv (interactionDesign false x ⬝ᵥ ξ₀)) -
          averagingGap g Q.covLaw (fun x => ginv (interactionDesign true x ⬝ᵥ ξ₀)))) := by
  have : IsProbabilityMeasure Q.covLaw := by unfold Population.covLaw; infer_instance
  set m : Bool → (Fin p → ℝ) → ℝ := fun t x => ginv (interactionDesign t x ⬝ᵥ ξ₀)
  have hγ : TendstoInMeasure P (fun n ω => interactionEffect (ξh n ω)) atTop
      (fun _ => interactionEffect ξ₀) :=
    hξ.comp_continuousAt (g := interactionEffect) (continuous_apply _).continuousAt
  have hβ : TendstoInMeasure P (fun n ω => interactionModifier (ξh n ω)) atTop
      (fun _ => interactionModifier ξ₀) :=
    hξ.comp_continuousAt (g := interactionModifier)
      (continuous_pi fun j => continuous_apply _).continuousAt
  have hlim := tendstoInMeasure_plugIn (αh := fun n ω => interactionIntercept (ξh n ω))
    (β₁h := fun n ω => interactionMain (ξh n ω)) (α := interactionIntercept ξ₀)
    (β₁ := interactionMain ξ₀) hg hγ hβ hx
  simp only [← interactionDesign_dotProduct] at hlim
  obtain ⟨hi₀, hv₀⟩ := integral_covLaw_eq_armMean_of_trial hT.measurable_X hX₂ hYQ₀
    (hT.isCondMean hYi hreg false) hsi₀ hov
  obtain ⟨hi₁, hv₁⟩ := integral_covLaw_eq_armMean_of_trial hT.measurable_X hX₂ hYQ₁
    (hT.isCondMean hYi hreg true) hsi₁ hov
  have hgap := (plugInEffect_sub_linkMarginal hν (g := g) (m := m)
    (α := interactionIntercept ξ₀) (γ := interactionEffect ξ₀) (β₁ := interactionMain ξ₀)
    (β₂ := interactionModifier ξ₀) (fun t x => by
      change g (ginv _) = _
      rw [hg, interactionDesign_dotProduct]) fun t => by
      cases t
      · exact hi₀
      · exact hi₁).2
  have hlm : linkMarginal g Q.covLaw (m false) (m true) = Q.marginalEffect g s₀ s₁ := by
    simp only [linkMarginal, Population.marginalEffect]
    rw [hv₀, hv₁]
  have e : plugInEffect g Q.covLaw (m false) (m true) = Q.marginalEffect g s₀ s₁ +
      (averagingGap g Q.covLaw (m false) - averagingGap g Q.covLaw (m true)) := by
    rw [← hgap, ← hlm]; ring
  rw [← e]
  exact hlim

/-- **The conditional plug-in at the mean of a target sample.** Under the hypotheses of
`tendstoInMeasure_conditionalPlugIn`, with the target covariate mean computed from `m n → ∞`
i.i.d. draws `X'` with law `Q_X` on the probability space of the trial sample (no independence
between the two is needed), the conditional plug-in converges in probability to
`Δ_Q + J_g(m₀) - J_g(m₁)`. -/
theorem tendstoInMeasure_conditionalPlugIn_sampleMean [IsProbabilityMeasure T.μ]
    [IsProbabilityMeasure Q.μ] [IsProbabilityMeasure P] (hT : T.IsRandomizedTwoArm)
    (hYi : ∀ t, Integrable (T.Y t) T.μ) {g ginv : ℝ → ℝ} (hg : ∀ s, g (ginv s) = s)
    {ξ₀ : Option (Fin p) ⊕ Option (Fin p) → ℝ}
    (hreg : IsOutcomeRegression T.μ T.A T.X T.obsOutcome
      fun t x => ginv (interactionDesign t x ⬝ᵥ ξ₀))
    (hX₂ : Measurable Q.X) {s₀ s₁ : ι} (hYQ₀ : Integrable (Q.Y s₀) Q.μ)
    (hYQ₁ : Integrable (Q.Y s₁) Q.μ)
    (hsi₀ : StructurallyInvariant T.μ T.X (T.Y false) Q.μ Q.X (Q.Y s₀))
    (hsi₁ : StructurallyInvariant T.μ T.X (T.Y true) Q.μ Q.X (Q.Y s₁))
    (hov : Q.covLaw ≪ T.covLaw) (hν : ∀ k, Integrable (fun x : Fin p → ℝ => x k) Q.covLaw)
    {ξh : ℕ → Ξ → Option (Fin p) ⊕ Option (Fin p) → ℝ}
    (hξ : TendstoInMeasure P ξh atTop fun _ => ξ₀) {Xs : ℕ → Ξ → Fin p → ℝ}
    (hXs : IsIIDSample Xs P) (hlawX : P.map (Xs 0) = Q.covLaw) {m : ℕ → ℕ}
    (hm : Tendsto m atTop atTop) :
    TendstoInMeasure P
      (fun n ω => linkContrast g (fun x => ginv (interactionDesign false x ⬝ᵥ ξh n ω))
        (fun x => ginv (interactionDesign true x ⬝ᵥ ξh n ω))
        (fun k => sampleMean (fun x => x k) Xs (m n) ω)) atTop
      (fun _ => Q.marginalEffect g s₀ s₁ +
        (averagingGap g Q.covLaw (fun x => ginv (interactionDesign false x ⬝ᵥ ξ₀)) -
          averagingGap g Q.covLaw (fun x => ginv (interactionDesign true x ⬝ᵥ ξ₀)))) := by
  have hν' : ∀ k, Integrable (fun x : Fin p → ℝ => x k) (P.map (Xs 0)) := fun k => by
    rw [hlawX]; exact hν k
  have hx : TendstoInMeasure P (fun n ω k => sampleMean (fun x : Fin p → ℝ => x k) Xs (m n) ω)
      atTop (fun _ => covMean Q.covLaw) := by
    have h := tendstoInMeasure_comp_tendsto_atTop (tendstoInMeasure_sampleMean_coord hXs hν') hm
    rw [hlawX] at h
    exact h
  exact tendstoInMeasure_conditionalPlugIn hT hYi hg hreg hX₂ hYQ₀ hYQ₁ hsi₀ hsi₁ hov hν hξ hx

/-- **The plug-in of the least squares coefficient at the target mean is consistent on the
identity link.** In a randomized trial with a linear outcome model over the interaction design
(`Trial.LinearOutcomeModel interactionDesign ξ₀`) and an i.i.d. sample of its individual records,
with both arms transported to the target (`false ↦ s₀`, `true ↦ s₁`), integrable target
outcomes, target covariates with integrable coordinates, and a reported target covariate mean
converging in probability to `x̄`, the estimated treatment effect at the mean,
`z(true, x̂)ᵀξ̂ - z(false, x̂)ᵀξ̂ = γ̂ + x̂ᵀβ̂₂`, converges in probability to the target mean
difference `E_Q[Y(s₁)] - E_Q[Y(s₀)]`: on the identity link the averaging gaps vanish. -/
theorem tendstoInMeasure_conditionalPlugIn_leastSquares [IsProbabilityMeasure T.μ]
    [IsProbabilityMeasure Q.μ] [IsProbabilityMeasure P] (hT : T.IsRandomizedTwoArm)
    {ξ₀ : Option (Fin p) ⊕ Option (Fin p) → ℝ}
    (hM : T.LinearOutcomeModel interactionDesign ξ₀) {O : ℕ → Ξ → (Fin p → ℝ) × Bool × ℝ}
    (hO : IsIIDSample O P) (hlaw : P.map (O 0) = T.ipdLaw) (hX₂ : Measurable Q.X) {s₀ s₁ : ι}
    (hYQ₀ : Integrable (Q.Y s₀) Q.μ) (hYQ₁ : Integrable (Q.Y s₁) Q.μ)
    (hsi₀ : StructurallyInvariant T.μ T.X (T.Y false) Q.μ Q.X (Q.Y s₀))
    (hsi₁ : StructurallyInvariant T.μ T.X (T.Y true) Q.μ Q.X (Q.Y s₁))
    (hov : Q.covLaw ≪ T.covLaw) (hν : ∀ k, Integrable (fun x : Fin p → ℝ => x k) Q.covLaw)
    {xh : ℕ → Ξ → Fin p → ℝ} (hx : TendstoInMeasure P xh atTop fun _ => covMean Q.covLaw) :
    TendstoInMeasure P
      (fun n ω =>
        interactionDesign true (xh n ω) ⬝ᵥ
            leastSquaresFit (recordDesign interactionDesign) recordResponse O n ω -
          interactionDesign false (xh n ω) ⬝ᵥ
            leastSquaresFit (recordDesign interactionDesign) recordResponse O n ω) atTop
      (fun _ => Q.armMean s₁ - Q.armMean s₀) := by
  have : IsProbabilityMeasure Q.covLaw := by unfold Population.covLaw; infer_instance
  have h := tendstoInMeasure_conditionalPlugIn (g := id) (ginv := id) hT hM.integrable_Y
    (fun _ => rfl) hM.isOutcomeRegression hX₂ hYQ₀ hYQ₁ hsi₀ hsi₁ hov hν
    (hM.tendstoInMeasure hT hO hlaw) hx
  have hgap : ∀ t, averagingGap id Q.covLaw (fun x => interactionDesign t x ⬝ᵥ ξ₀) = 0 :=
    fun t => by simp [averagingGap]
  simp only [id, hgap, sub_self, add_zero, Population.marginalEffect, linkContrast] at h
  exact h

end Limit

end PopulationAdjustment

end CausalInference
