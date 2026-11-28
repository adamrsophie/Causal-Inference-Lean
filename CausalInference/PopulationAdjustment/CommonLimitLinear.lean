/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.PopulationAdjustment.WeightedConsistencyContrast
public import CausalInference.PopulationAdjustment.StandardizationConsistencyLeastSquares
public import CausalInference.PopulationAdjustment.StandardizationConsistencyConditional

/-!
# The common limit of weighting and standardization for a linear outcome model

The index trial `T` randomizes the arms `true` and `false`; an i.i.d. sample `O` of its records
`(X, A, Y)` is used twice. The **weighted estimate** of the target mean of arm `a` is the
weighted arm mean with the entropy balancing weights at the reported target feature means `t`
(`sampleBalancedArmMean`); the **standardized estimate** is the least squares fit `ξ̂` of the
linear outcome model `E[Y | X, A] = z(A, X)ᵀξ₀`, averaged over the target covariate law `Q_X`:
`∫ z(a, x)ᵀξ̂ dQ_X`.

When the regression of each arm is affine in the matched features,
`z(a, x)ᵀξ₀ = α_a + β_aᵀφ(x)`, and each arm of the trial is transported to the target (absolute
constancy and overlap), both estimates converge in probability to the target arm mean
`E_Q[Y(s)]`, and their difference converges in probability to `0`
(`commonLimit_leastSquares_armMean`). The same holds for the unanchored and anchored comparisons
on any link scale continuous at the target means (`commonLimit_leastSquares_unanchored`,
`commonLimit_leastSquares_anchored`), and on the identity scale under relative constancy only
(`commonLimit_leastSquares_anchored_identity`), where the standardization half is
`tendstoInMeasure_leastSquares_contrast_identity`.

**Conditions.** One set of conditions on the law of the trial makes both consistency
theorems apply.

* Shared: randomization (`Trial.IsRandomizedTwoArm`); potential outcomes with finite second
  moments; the correct linear regression `E[Y | X, A] = z(A, X)ᵀξ₀`; an i.i.d. sample of the
  individual data; and, in the target, a probability law with measurable covariates, integrable
  outcomes, absolute constancy of each arm used and overlap `Q_X ≪ T_X`.
* Standardization only: the design of the outcome model (measurable coordinates with finite
  second moments, positive definite second moment), and design coordinates integrable under
  `Q_X`.
* Weighting only: a measurable sample, bounded measurable features `‖φ(x) - t‖ ≤ B`, the margin
  condition of `WeightedConsistencyFeasible` for the trial covariate law at `t`, a bounded
  conditional residual variance, the regression affine in the features, and `t` equal to the
  target feature means.

The regression on the law of the records, the square integrable residual, the independence of
covariates and arm in the records, the positive arm probabilities and the target conditional
mean functions are derived (`IsOutcomeRegression.condExp_ipdLaw`,
`Trial.LinearOutcomeModel.integrable_residual_sq`, `IndirectComparison.Population.IsCondMean`
from `Trial.IsRandomizedTwoArm.isCondMean`). For the interaction design in the features
`z(a, x) = (1, φ(x), 1[a], 1[a]φ(x))` the design conditions are derived as well, the positive
definite design second moment from the margin condition
(`posDef_featureInteractionDesign_gram`), so that the final statements
(`commonLimit_interaction_armMean` and the comparisons of `CommonLimitIdentified`) take the
primitive conditions only.

## Main definitions

* `featureInteractionDesign`: the interaction design `(1, φ(x), 1[a], 1[a]φ(x))` in the features.

## Main results

* `condExp_map_ae_eq`, `IsOutcomeRegression.condExp_ipdLaw`: the regression on the law of the
  records.
* `Trial.LinearOutcomeModel.isConsistent_balanced`, `Trial.LinearOutcomeModel.isCondMean_target`.
* `commonLimit_leastSquares_armMean`, `commonLimit_leastSquares_unanchored`,
  `commonLimit_leastSquares_anchored`, `commonLimit_leastSquares_anchored_identity`,
  `tendstoInMeasure_leastSquares_contrast_identity`.
* `eq_zero_of_ae_affine_of_margin`, `posDef_featureInteractionDesign_gram`,
  `Trial.linearOutcomeModel_featureInteraction`, `commonLimit_interaction_armMean`.

## References

* J. E. Signorovitch and coauthors, PharmacoEconomics 28 (2010).
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

/-! ### Conditional expectations on the law of a record -/

section Records

variable {Ω D C : Type*} [MeasurableSpace Ω] [MeasurableSpace D] [MeasurableSpace C]

/-- **A conditional expectation carries over to the law of a record.** If `f` is a measurable
record map, `r` a measurable response of a record with `r ∘ f` integrable, `π` a measurable
function of a record, and `E[r ∘ f | π ∘ f] = h ∘ π ∘ f` almost surely, then under the law of
the record `E[r | π] = h ∘ π` almost surely. -/
theorem condExp_map_ae_eq {μ : Measure Ω} [IsFiniteMeasure μ] {f : Ω → D} (hf : Measurable f)
    {π : D → C} (hπ : Measurable π) {r : D → ℝ} (hr : Measurable r)
    (hri : Integrable (r ∘ f) μ) {h : C → ℝ} (hh : Measurable h)
    (hcond : μ[r ∘ f | MeasurableSpace.comap (π ∘ f) inferInstance] =ᵐ[μ] h ∘ π ∘ f) :
    (μ.map f)[r | MeasurableSpace.comap π inferInstance] =ᵐ[μ.map f] h ∘ π := by
  have hle : MeasurableSpace.comap π inferInstance ≤ (inferInstance : MeasurableSpace D) :=
    hπ.comap_le
  have hle' : MeasurableSpace.comap (π ∘ f) inferInstance ≤ (inferInstance : MeasurableSpace Ω) :=
    (hπ.comp hf).comap_le
  have hhπ : Measurable (h ∘ π) := hh.comp hπ
  have hint : Integrable (h ∘ π ∘ f) μ := integrable_condExp.congr hcond
  have hint' : Integrable (h ∘ π) (μ.map f) :=
    (integrable_map_measure hhπ.aestronglyMeasurable hf.aemeasurable).2 hint
  have hrm : Integrable r (μ.map f) :=
    (integrable_map_measure hr.aestronglyMeasurable hf.aemeasurable).2 hri
  refine (ae_eq_condExp_of_forall_setIntegral_eq hle hrm (fun s _ _ => hint'.integrableOn)
    (fun s hs _ => ?_) ?_).symm
  · obtain ⟨B, hB, rfl⟩ := hs
    have hpB : MeasurableSet (π ⁻¹' B) := hπ hB
    rw [setIntegral_map hpB hhπ.aestronglyMeasurable hf.aemeasurable,
      setIntegral_map hpB hr.aestronglyMeasurable hf.aemeasurable]
    have hs' : MeasurableSet[MeasurableSpace.comap (π ∘ f) inferInstance] (f ⁻¹' (π ⁻¹' B)) :=
      ⟨B, hB, rfl⟩
    change _ = ∫ x in f ⁻¹' (π ⁻¹' B), (r ∘ f) x ∂μ
    rw [← setIntegral_condExp hle' hri hs']
    exact setIntegral_congr_ae (hf (hπ hB)) (hcond.mono fun ω hω _ => hω.symm)
  · exact ((hh.comp (comap_measurable π)).stronglyMeasurable).aestronglyMeasurable

variable {𝒳 : Type*} [MeasurableSpace 𝒳]

/-- **The observed regression of a trial is the regression of its individual data**: if `m` is
a version of `E[Y | X, A]` in the trial (`PointTreatment.IsOutcomeRegression`) and the observed
outcome is integrable, then `m(A, X)` is a version of the regression of the outcome on the
covariates and the arm under the law `Trial.ipdLaw` of the records. -/
theorem _root_.CausalInference.PointTreatment.IsOutcomeRegression.condExp_ipdLaw
    {T : Trial Ω 𝒳 Bool} [IsFiniteMeasure T.μ] (hX : Measurable T.X) (hA : Measurable T.A)
    (hYo : Measurable T.obsOutcome) (hYi : Integrable T.obsOutcome T.μ) {m : Bool → 𝒳 → ℝ}
    (hreg : IsOutcomeRegression T.μ T.A T.X T.obsOutcome m) :
    T.ipdLaw[fun z => z.2.2 | MeasurableSpace.comap
      (fun z : 𝒳 × Bool × ℝ => (z.1, z.2.1)) inferInstance] =ᵐ[T.ipdLaw]
        fun z => m z.2.1 z.1 := by
  have hm : Measurable fun q : 𝒳 × Bool => m q.2 q.1 :=
    measurable_from_prod_countable_left (f := fun q : 𝒳 × Bool => m q.2 q.1) hreg.1
  exact condExp_map_ae_eq (f := fun ω => (T.X ω, T.A ω, T.obsOutcome ω))
    (hX.prodMk (hA.prodMk hYo)) (measurable_fst.prodMk measurable_snd.fst)
    measurable_snd.snd hYi hm hreg.2

end Records

/-! ### The trial with a linear outcome model -/

section Model

variable {Ω₁ 𝒳 κ : Type*} [MeasurableSpace Ω₁] [MeasurableSpace 𝒳] [Fintype κ]
  {T : Trial Ω₁ 𝒳 Bool} {z : Bool → 𝒳 → κ → ℝ} {ξ₀ : κ → ℝ}

/-- The linear surfaces `z(a, ·)ᵀξ` are measurable. -/
theorem measurable_linearSurface (hz : ∀ a j, Measurable fun x => z a x j) (ξ : κ → ℝ)
    (a : Bool) : Measurable fun x => z a x ⬝ᵥ ξ :=
  Finset.measurable_sum _ fun j _ => (hz a j).mul_const _

/-- **The residual of a linear outcome model is square integrable on the records**: under a
randomized trial with a linear outcome model, `(Y - z(A, X)ᵀξ₀)²` is integrable under the law of
the records. -/
theorem _root_.CausalInference.IndirectComparison.Trial.LinearOutcomeModel.integrable_residual_sq
    (hM : T.LinearOutcomeModel z ξ₀) (hT : T.IsRandomizedTwoArm) :
    Integrable (fun o : 𝒳 × Bool × ℝ => (o.2.2 - z o.2.1 o.1 ⬝ᵥ ξ₀) ^ 2) T.ipdLaw := by
  have hYo : Measurable T.obsOutcome :=
    measurable_obsOutcome (A := T.A) (Y := T.Y) hT.measurable_A hT.measurable_Y
  have hf : Measurable fun ω => (T.X ω, T.A ω, T.obsOutcome ω) :=
    hT.measurable_X.prodMk (hT.measurable_A.prodMk hYo)
  have hzm : ∀ j, Measurable fun o : 𝒳 × Bool × ℝ => z o.2.1 o.1 j := fun j =>
    (measurable_from_prod_countable_left (f := fun q : 𝒳 × Bool => z q.2 q.1 j)
      fun a => hM.measurable_z a j).comp (measurable_fst.prodMk measurable_snd.fst)
  have hgm : Measurable fun o : 𝒳 × Bool × ℝ => (o.2.2 - z o.2.1 o.1 ⬝ᵥ ξ₀) ^ 2 :=
    (measurable_snd.snd.sub (Finset.measurable_sum _ fun j _ => (hzm j).mul_const _)).pow_const 2
  rw [Trial.ipdLaw, integrable_map_measure hgm.aestronglyMeasurable hf.aemeasurable]
  have hY2 : MemLp T.obsOutcome 2 T.μ :=
    memLp_two_select hT.measurable_A hT.measurable_Y hM.memLp_Y
  have hz2 : ∀ j, MemLp (fun ω => z (T.A ω) (T.X ω) j) 2 T.μ := fun j =>
    memLp_two_select (f := fun a ω => z a (T.X ω) j) hT.measurable_A
      (fun a => (hM.measurable_z a j).comp hT.measurable_X) fun a => hM.memLp_z a j
  have hd2 : MemLp (fun ω => z (T.A ω) (T.X ω) ⬝ᵥ ξ₀) 2 T.μ := by
    simp only [dotProduct]
    exact memLp_finsetSum _ fun j _ => (hz2 j).mul_const _
  exact (hY2.sub hd2).integrable_sq

end Model

/-- **Two estimators with the same limit have a difference converging to zero**: if `X̂ → c`
and `Ŷ → c` in probability, then `X̂ - Ŷ → 0` in probability. -/
theorem tendstoInMeasure_sub_zero_of_same_limit {Ξ : Type*} [MeasurableSpace Ξ] {P : Measure Ξ}
    {X Y : ℕ → Ξ → ℝ} {c : ℝ} (hX : TendstoInMeasure P X atTop fun _ => c)
    (hY : TendstoInMeasure P Y atTop fun _ => c) :
    TendstoInMeasure P (fun n ω => X n ω - Y n ω) atTop fun _ => 0 := by
  have h := hX.sub hY
  simp only [Pi.sub_def, sub_self] at h
  exact h

/-! ### The randomized trial -/

section Randomized

variable {Ω₁ 𝒳 : Type*} [MeasurableSpace Ω₁] [MeasurableSpace 𝒳]

/-- Both arms of a randomized two arm trial have positive probability. -/
theorem _root_.CausalInference.IndirectComparison.Trial.IsRandomizedTwoArm.prob_arm_pos
    {T : Trial Ω₁ 𝒳 Bool} [IsProbabilityMeasure T.μ] (hT : T.IsRandomizedTwoArm) (a : Bool) :
    0 < T.μ.real (T.A ⁻¹' {a}) := by
  cases a
  · have hs : MeasurableSet (T.A ⁻¹' {true}) := hT.measurable_A (measurableSet_singleton _)
    have e : T.A ⁻¹' {false} = (T.A ⁻¹' {true})ᶜ := by ext ω; simp
    have h := probReal_add_probReal_compl (μ := T.μ) hs
    rw [e]
    linarith [hT.prob_lt_one]
  · exact hT.prob_pos

/-- In a randomized two arm trial the covariates are independent of the assignment. -/
theorem _root_.CausalInference.IndirectComparison.Trial.IsRandomizedTwoArm.indepFun_X_A
    {T : Trial Ω₁ 𝒳 Bool} (hT : T.IsRandomizedTwoArm) : IndepFun T.X T.A T.μ :=
  (hT.indepFun.comp measurable_id measurable_fst).symm

end Randomized

/-! ### The interaction design in the features -/

section Interaction

variable {Ω₁ 𝒳 : Type*} [MeasurableSpace Ω₁] [MeasurableSpace 𝒳] {p : ℕ}
  {φ : 𝒳 → Fin p → ℝ} {t : Fin p → ℝ}

/-- **The margin condition rules out an almost surely affine relation of the features.** If the
margin condition holds at `t` for a probability law `ν` and `c + wᵀφ(x) = 0` for `ν`-almost
every `x`, then `w = 0` and `c = 0`. -/
theorem eq_zero_of_ae_affine_of_margin {ν : Measure 𝒳} [IsProbabilityMeasure ν]
    (hφ : Measurable φ) {δ : ℝ} (hδ : 0 < δ)
    (hmargin : ∀ v : Fin p → ℝ, ‖v‖ = 1 → δ ≤ ν.real {x | δ ≤ v ⬝ᵥ (φ x - t)}) {c : ℝ}
    {w : Fin p → ℝ} (h : ∀ᵐ x ∂ν, c + w ⬝ᵥ φ x = 0) : w = 0 ∧ c = 0 := by
  have hset : ∀ v : Fin p → ℝ, MeasurableSet {x : 𝒳 | δ ≤ v ⬝ᵥ (φ x - t)} := fun v =>
    measurableSet_le measurable_const
      ((continuous_const.dotProduct continuous_id).measurable.comp (hφ.sub_const t))
  -- a point of a set of positive measure where the relation holds
  have hpt : ∀ v : Fin p → ℝ, ‖v‖ = 1 → ∃ x, c + w ⬝ᵥ φ x = 0 ∧ δ ≤ v ⬝ᵥ (φ x - t) := by
    intro v hv
    have hpos : ν {x | δ ≤ v ⬝ᵥ (φ x - t)} ≠ 0 := by
      intro h0
      have h1 := hmargin v hv
      rw [measureReal_def, h0, ENNReal.toReal_zero] at h1
      linarith
    have hne : ν.restrict {x | δ ≤ v ⬝ᵥ (φ x - t)} ≠ 0 := by
      rwa [Ne, Measure.restrict_eq_zero]
    have := ae_neBot.2 hne
    obtain ⟨x, hx1, hx2⟩ := ((ae_restrict_of_ae h).and (ae_restrict_mem (hset v))).exists
    exact ⟨x, hx1, hx2⟩
  have hw : w = 0 := by
    by_contra hw0
    have hn : 0 < ‖w‖ := norm_pos_iff.2 hw0
    set u : Fin p → ℝ := ‖w‖⁻¹ • w with hu
    have hun : ‖u‖ = 1 := by
      rw [hu, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hn.ne']
    have hun' : ‖-u‖ = 1 := by rw [norm_neg, hun]
    obtain ⟨x₁, h₁, h₁'⟩ := hpt u hun
    obtain ⟨x₂, h₂, h₂'⟩ := hpt (-u) hun'
    have e : ∀ x, c + w ⬝ᵥ φ x = 0 → u ⬝ᵥ (φ x - t) = -(‖w‖⁻¹ * c) - u ⬝ᵥ t := by
      intro x hx
      rw [dotProduct_sub, hu, smul_dotProduct, smul_eq_mul]
      have : w ⬝ᵥ φ x = -c := by linarith
      rw [this]; ring
    rw [neg_dotProduct] at h₂'
    have := e x₁ h₁
    have := e x₂ h₂
    linarith
  refine ⟨hw, ?_⟩
  subst hw
  obtain ⟨x, hx⟩ := (h.and (ae_of_all ν fun _ => trivial)).exists
  simpa using hx.1

/-- The **interaction design in the features**: the row `(1, φ(x), 1[a], 1[a]φ(x))` of arm `a`
at `x`. -/
def featureInteractionDesign (φ : 𝒳 → Fin p → ℝ) (a : Bool) (x : 𝒳) :
    Option (Fin p) ⊕ Option (Fin p) → ℝ :=
  interactionDesign a (φ x)

omit [MeasurableSpace 𝒳] in
/-- **The regression of the interaction design is affine in the features**:
`z(a, x)ᵀξ = (α + 1[a]γ) + (β₁ + 1[a]β₂)ᵀφ(x)` with the coefficients read off `ξ`. -/
theorem featureInteractionDesign_dotProduct (φ : 𝒳 → Fin p → ℝ) (a : Bool) (x : 𝒳)
    (ξ : Option (Fin p) ⊕ Option (Fin p) → ℝ) :
    featureInteractionDesign φ a x ⬝ᵥ ξ =
      (interactionIntercept ξ + if a then interactionEffect ξ else 0) +
        (interactionMain ξ + if a then interactionModifier ξ else 0) ⬝ᵥ φ x := by
  rw [featureInteractionDesign, interactionDesign_dotProduct]
  cases a
  · simp [interactionPredictor, dotProduct, mul_comm]
  · simp only [interactionPredictor, dotProduct, ite_true, Pi.add_apply, add_mul]
    rw [Finset.sum_add_distrib]
    simp only [mul_comm]
    ring

/-- The coordinates of the interaction design are measurable for measurable features. -/
theorem measurable_featureInteractionDesign (hφ : Measurable φ) (a : Bool)
    (k : Option (Fin p) ⊕ Option (Fin p)) :
    Measurable fun x => featureInteractionDesign φ a x k :=
  (measurable_interactionDesign a k).comp hφ

omit [MeasurableSpace 𝒳] in
/-- The coordinates of the interaction design are bounded by `1 + B + ‖t‖` for features with
`‖φ(x) - t‖ ≤ B`. -/
theorem abs_featureInteractionDesign_le {B : ℝ} (hB : ∀ x, ‖φ x - t‖ ≤ B) (a : Bool) (x : 𝒳)
    (k : Option (Fin p) ⊕ Option (Fin p)) :
    |featureInteractionDesign φ a x k| ≤ 1 + B + ‖t‖ := by
  have hφx : ∀ j, |φ x j| ≤ B + ‖t‖ := fun j => by
    calc |φ x j| = ‖φ x j‖ := (Real.norm_eq_abs _).symm
      _ ≤ ‖φ x‖ := norm_le_pi_norm (φ x) j
      _ = ‖(φ x - t) + t‖ := by rw [sub_add_cancel]
      _ ≤ B + ‖t‖ := (norm_add_le _ _).trans (by linarith [hB x])
  have hB0 : 0 ≤ B + ‖t‖ := by
    have := (norm_nonneg (φ x - t)).trans (hB x)
    linarith [norm_nonneg t]
  rcases k with (_ | j) | (_ | j) <;> cases a <;>
    simp only [featureInteractionDesign, interactionDesign, Bool.false_eq_true, ↓reduceIte,
      abs_one, abs_zero]
  all_goals first | linarith | linarith [hφx j]

/-- **The design second moment of the interaction design is positive definite** in a randomized
trial whose covariate law satisfies the margin condition at `t`, for bounded measurable
features. If `z(A, X)ᵀv = 0` almost surely, randomization gives `z(a, X)ᵀv = 0` almost surely in
each arm, and the margin condition forces each of the two affine functions of the features to
vanish, so `v = 0`. -/
theorem posDef_featureInteractionDesign_gram {T : Trial Ω₁ 𝒳 Bool} [IsProbabilityMeasure T.μ]
    (hT : T.IsRandomizedTwoArm) (hφ : Measurable φ) {B : ℝ} (hB : ∀ x, ‖φ x - t‖ ≤ B) {δ : ℝ}
    (hδ : 0 < δ)
    (hmargin : ∀ v : Fin p → ℝ, ‖v‖ = 1 → δ ≤ T.covLaw.real {x | δ ≤ v ⬝ᵥ (φ x - t)}) :
    (Matrix.of fun j k => ∫ ω, featureInteractionDesign φ (T.A ω) (T.X ω) j *
      featureInteractionDesign φ (T.A ω) (T.X ω) k ∂T.μ).PosDef := by
  have : IsProbabilityMeasure T.covLaw := T.isProbabilityMeasure_covLaw hT.measurable_X
  have hdm : ∀ k, Measurable fun ω => featureInteractionDesign φ (T.A ω) (T.X ω) k := fun k =>
    (measurable_from_prod_countable_left (f := fun q : 𝒳 × Bool =>
      featureInteractionDesign φ q.2 q.1 k)
      fun a => measurable_featureInteractionDesign hφ a k).comp
      (hT.measurable_X.prodMk hT.measurable_A)
  have hd2 : ∀ k, MemLp (fun ω => featureInteractionDesign φ (T.A ω) (T.X ω) k) 2 T.μ :=
    fun k => MemLp.of_bound (hdm k).aestronglyMeasurable (1 + B + ‖t‖)
      (ae_of_all _ fun ω => by
        rw [Real.norm_eq_abs]; exact abs_featureInteractionDesign_le hB _ _ k)
  refine posDef_gram_of_ae hd2 fun v hv => ?_
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

/-- **A trial with a correct linear regression in the interaction design of the features is a
linear outcome model**, for a randomized trial with potential outcomes of finite second moments,
bounded measurable features and the margin condition at `t` for the trial covariate law: the
measurability and the second moments of the design and the positive definite design second
moment are derived. -/
theorem _root_.CausalInference.IndirectComparison.Trial.linearOutcomeModel_featureInteraction
    {T : Trial Ω₁ 𝒳 Bool} [IsProbabilityMeasure T.μ] (hT : T.IsRandomizedTwoArm)
    (hY2 : ∀ a, MemLp (T.Y a) 2 T.μ) (hφ : Measurable φ) {B : ℝ} (hB : ∀ x, ‖φ x - t‖ ≤ B)
    {δ : ℝ} (hδ : 0 < δ)
    (hmargin : ∀ v : Fin p → ℝ, ‖v‖ = 1 → δ ≤ T.covLaw.real {x | δ ≤ v ⬝ᵥ (φ x - t)})
    {ξ₀ : Option (Fin p) ⊕ Option (Fin p) → ℝ}
    (hreg : IsOutcomeRegression T.μ T.A T.X T.obsOutcome
      fun a x => featureInteractionDesign φ a x ⬝ᵥ ξ₀) :
    T.LinearOutcomeModel (featureInteractionDesign φ) ξ₀ where
  measurable_z a k := measurable_featureInteractionDesign hφ a k
  memLp_z a k := MemLp.of_bound
    ((measurable_featureInteractionDesign hφ a k).comp hT.measurable_X).aestronglyMeasurable
    (1 + B + ‖t‖) (ae_of_all _ fun ω => by
      rw [Real.norm_eq_abs]; exact abs_featureInteractionDesign_le hB _ _ k)
  memLp_Y := hY2
  posDef := posDef_featureInteractionDesign_gram hT hφ hB hδ hmargin
  isOutcomeRegression := hreg

/-- The coordinates of the interaction design are integrable under every probability law, for
bounded measurable features. -/
theorem integrable_featureInteractionDesign {ν : Measure 𝒳} [IsProbabilityMeasure ν]
    (hφ : Measurable φ) {B : ℝ} (hB : ∀ x, ‖φ x - t‖ ≤ B) (a : Bool)
    (k : Option (Fin p) ⊕ Option (Fin p)) :
    Integrable (fun x => featureInteractionDesign φ a x k) ν :=
  (integrable_const (1 + B + ‖t‖)).mono'
    (measurable_featureInteractionDesign hφ a k).aestronglyMeasurable
    (ae_of_all _ fun x => by rw [Real.norm_eq_abs]; exact abs_featureInteractionDesign_le hB _ _ k)

end Interaction

/-! ### The two estimators under one set of conditions -/

section CommonLimit

variable {Ω₁ Ω₂ Ξ 𝒳 ι κ : Type*} [MeasurableSpace Ω₁] [MeasurableSpace Ω₂] [MeasurableSpace Ξ]
  [MeasurableSpace 𝒳] [Fintype κ] [DecidableEq κ] {p : ℕ} {T : Trial Ω₁ 𝒳 Bool}
  {Q : Population Ω₂ 𝒳 ι} {P : Measure Ξ} {O : ℕ → Ξ → 𝒳 × Bool × ℝ} {z : Bool → 𝒳 → κ → ℝ}
  {ξ₀ : κ → ℝ} {φ : 𝒳 → Fin p → ℝ} {t : Fin p → ℝ}

omit [DecidableEq κ] in
/-- **The weighted arm mean from the conditions on a trial with a linear outcome model.** In a
randomized trial with a linear outcome model, for a measurable i.i.d. sample of its individual
data, bounded measurable features with the margin condition at `t` for the trial covariate law,
a bounded conditional residual variance of the records, and the regression of arm `a` affine in
the features, `z(a, x)ᵀξ₀ = α + βᵀφ(x)`, the weighted arm mean is consistent for `α + βᵀt`. The
regression of the records, the square integrable residual, the independence of covariates and
arm and the positive arm probability are derived. -/
theorem _root_.CausalInference.IndirectComparison.Trial.LinearOutcomeModel.isConsistent_balanced
    [IsProbabilityMeasure T.μ] [IsProbabilityMeasure P] (hM : T.LinearOutcomeModel z ξ₀)
    (hT : T.IsRandomizedTwoArm) (hO : IsIIDSample O P) (hOm : ∀ i, Measurable (O i))
    (hlaw : P.map (O 0) = T.ipdLaw) (hφ : Measurable φ) {B : ℝ} (hB : ∀ x, ‖φ x - t‖ ≤ B)
    {δ : ℝ} (hδ : 0 < δ)
    (hmargin : ∀ v : Fin p → ℝ, ‖v‖ = 1 → δ ≤ T.covLaw.real {x | δ ≤ v ⬝ᵥ (φ x - t)})
    {σ2 : ℝ} (hvar : T.ipdLaw[fun o => (o.2.2 - z o.2.1 o.1 ⬝ᵥ ξ₀) ^ 2 |
      MeasurableSpace.comap (fun o : 𝒳 × Bool × ℝ => (o.1, o.2.1)) inferInstance]
        ≤ᵐ[T.ipdLaw] fun _ => σ2)
    (a : Bool) {α : ℝ} {β : Fin p → ℝ} (haff : ∀ x, z a x ⬝ᵥ ξ₀ = α + β ⬝ᵥ φ x) :
    IsConsistent (sampleBalancedArmMean φ t O a) (α + β ⬝ᵥ t) P := by
  have hYo : Measurable T.obsOutcome :=
    measurable_obsOutcome (A := T.A) (Y := T.Y) hT.measurable_A hT.measurable_Y
  exact sampleBalancedArmMean_isConsistent_trial hT.measurable_X hT.measurable_A hYo
    hT.indepFun_X_A hO hOm hlaw hφ hB hδ hmargin a (hT.prob_arm_pos a)
    (mu := fun a x => z a x ⬝ᵥ ξ₀) (measurable_linearSurface hM.measurable_z ξ₀)
    (hM.integrable_residual_sq hT)
    (hM.isOutcomeRegression.condExp_ipdLaw hT.measurable_X hT.measurable_A hYo
      (PointTreatment.integrable_obsOutcome (A := T.A) (Y := T.Y) hT.measurable_A
        hM.integrable_Y)) hvar haff

omit [DecidableEq κ] in
/-- **The regression of a transported arm is a target conditional mean function**: in a
randomized trial with a linear outcome model, absolute constancy of arm `a` of the trial and
treatment `s` of the target and overlap make `z(a, ·)ᵀξ₀` a conditional mean function of `Y(s)`
in the target. -/
theorem _root_.CausalInference.IndirectComparison.Trial.LinearOutcomeModel.isCondMean_target
    [IsProbabilityMeasure T.μ] (hM : T.LinearOutcomeModel z ξ₀) (hT : T.IsRandomizedTwoArm)
    (hX₂ : Measurable Q.X) {a : Bool} {s : ι}
    (hsi : StructurallyInvariant T.μ T.X (T.Y a) Q.μ Q.X (Q.Y s)) (hov : Q.covLaw ≪ T.covLaw) :
    Q.IsCondMean s fun x => z a x ⬝ᵥ ξ₀ :=
  Population.IsCondMean.of_structurallyInvariant (P := ⟨T.μ, T.X, fun _ => T.Y a⟩) (t := s)
    hT.measurable_X hX₂ (hT.isCondMean hM.integrable_Y hM.isOutcomeRegression a) hsi hov

/-- **Weighting and standardization share their limit: the target arm mean.** Let `T` be a
randomized trial with a linear outcome model `E[Y | X, A] = z(A, X)ᵀξ₀`
(`Trial.LinearOutcomeModel`), `O` a measurable i.i.d. sample of its individual data, `φ` bounded
measurable features with the margin condition at `t` for the trial covariate law, the
conditional residual variance of the records bounded, and the regression of arm `a` affine in the
features, `z(a, x)ᵀξ₀ = α + βᵀφ(x)`. Let `Q` be a target population with probability law,
measurable covariates, feature means `t`, integrable `Y(s)`, design coordinates of arm `a`
integrable under `Q_X`, absolute constancy of arm `a` of the trial and treatment `s` of the
target, and overlap `Q_X ≪ T_X`. Then the weighted arm mean and the standardized least squares
fit `∫ z(a, x)ᵀξ̂ dQ_X` both converge in probability to `E_Q[Y(s)]`, and their difference
converges in probability to `0`. -/
theorem commonLimit_leastSquares_armMean [IsProbabilityMeasure T.μ] [IsProbabilityMeasure P]
    [IsProbabilityMeasure Q.μ] (hT : T.IsRandomizedTwoArm) (hM : T.LinearOutcomeModel z ξ₀)
    (hO : IsIIDSample O P) (hOm : ∀ i, Measurable (O i)) (hlaw : P.map (O 0) = T.ipdLaw)
    (hφ : Measurable φ) {B : ℝ} (hB : ∀ x, ‖φ x - t‖ ≤ B) {δ : ℝ} (hδ : 0 < δ)
    (hmargin : ∀ v : Fin p → ℝ, ‖v‖ = 1 → δ ≤ T.covLaw.real {x | δ ≤ v ⬝ᵥ (φ x - t)})
    {σ2 : ℝ} (hvar : T.ipdLaw[fun o => (o.2.2 - z o.2.1 o.1 ⬝ᵥ ξ₀) ^ 2 |
      MeasurableSpace.comap (fun o : 𝒳 × Bool × ℝ => (o.1, o.2.1)) inferInstance]
        ≤ᵐ[T.ipdLaw] fun _ => σ2)
    (a : Bool) {α : ℝ} {β : Fin p → ℝ} (haff : ∀ x, z a x ⬝ᵥ ξ₀ = α + β ⬝ᵥ φ x)
    (hX₂ : Measurable Q.X) (ht : ∀ k, ∫ x, φ x k ∂Q.covLaw = t k)
    (hzQ : ∀ j, Integrable (fun x => z a x j) Q.covLaw) {s : ι} (hYQ : Integrable (Q.Y s) Q.μ)
    (hsi : StructurallyInvariant T.μ T.X (T.Y a) Q.μ Q.X (Q.Y s)) (hov : Q.covLaw ≪ T.covLaw) :
    IsConsistent (sampleBalancedArmMean φ t O a) (Q.armMean s) P ∧
      TendstoInMeasure P (fun n ω => ∫ x, z a x ⬝ᵥ
        leastSquaresFit (recordDesign z) recordResponse O n ω ∂Q.covLaw) atTop
        (fun _ => Q.armMean s) ∧
      TendstoInMeasure P (fun n ω => ∫ x, z a x ⬝ᵥ
        leastSquaresFit (recordDesign z) recordResponse O n ω ∂Q.covLaw -
          sampleBalancedArmMean φ t O a n ω) atTop (fun _ => 0) := by
  have hW := hM.isConsistent_balanced hT hO hOm hlaw hφ hB hδ hmargin hvar a haff
  rw [← integral_affine_covLaw hφ hB ht haff,
    (hM.isCondMean_target hT hX₂ hsi hov).integral_eq hX₂ hYQ] at hW
  have hS := tendstoInMeasure_leastSquares_armMean hT hM hO hlaw hX₂ hYQ hsi hov hzQ
  exact ⟨hW, hS, tendstoInMeasure_sub_zero_of_same_limit hS hW⟩

/-- **The unanchored comparisons share their limit.** Under the hypotheses of
`commonLimit_leastSquares_armMean` for the index arm `true ↦ a`, with a reported mean `m̂_b` of
treatment `b` in the target converging in probability to `E_Q[Y(b)]` and a link `g` continuous
at the two target means, the weighted comparison `g(m̂_b) - g(μ̂_true)` and the standardized
comparison `g(m̂_b) - g(∫ z(true, x)ᵀξ̂ dQ_X)` both converge in probability to the target
marginal effect of `b` relative to `a`, and their difference converges in probability to `0`. -/
theorem commonLimit_leastSquares_unanchored [IsProbabilityMeasure T.μ] [IsProbabilityMeasure P]
    [IsProbabilityMeasure Q.μ] (hT : T.IsRandomizedTwoArm) (hM : T.LinearOutcomeModel z ξ₀)
    (hO : IsIIDSample O P) (hOm : ∀ i, Measurable (O i)) (hlaw : P.map (O 0) = T.ipdLaw)
    (hφ : Measurable φ) {B : ℝ} (hB : ∀ x, ‖φ x - t‖ ≤ B) {δ : ℝ} (hδ : 0 < δ)
    (hmargin : ∀ v : Fin p → ℝ, ‖v‖ = 1 → δ ≤ T.covLaw.real {x | δ ≤ v ⬝ᵥ (φ x - t)})
    {σ2 : ℝ} (hvar : T.ipdLaw[fun o => (o.2.2 - z o.2.1 o.1 ⬝ᵥ ξ₀) ^ 2 |
      MeasurableSpace.comap (fun o : 𝒳 × Bool × ℝ => (o.1, o.2.1)) inferInstance]
        ≤ᵐ[T.ipdLaw] fun _ => σ2)
    {α : ℝ} {β : Fin p → ℝ} (haff : ∀ x, z true x ⬝ᵥ ξ₀ = α + β ⬝ᵥ φ x)
    (hX₂ : Measurable Q.X) (ht : ∀ k, ∫ x, φ x k ∂Q.covLaw = t k)
    (hzQ : ∀ j, Integrable (fun x => z true x j) Q.covLaw) {a b : ι}
    (hYQ : Integrable (Q.Y a) Q.μ)
    (hsi : StructurallyInvariant T.μ T.X (T.Y true) Q.μ Q.X (Q.Y a)) (hov : Q.covLaw ≪ T.covLaw)
    {mb : ℕ → Ξ → ℝ} (hmb : TendstoInMeasure P mb atTop fun _ => Q.armMean b) {g : ℝ → ℝ}
    (hga : ContinuousAt g (Q.armMean a)) (hgb : ContinuousAt g (Q.armMean b)) :
    IsConsistent (unanchoredBalancedEstimate g φ t O mb) (Q.marginalEffect g a b) P ∧
      TendstoInMeasure P (fun n ω => g (mb n ω) - g (∫ x, z true x ⬝ᵥ
        leastSquaresFit (recordDesign z) recordResponse O n ω ∂Q.covLaw)) atTop
        (fun _ => Q.marginalEffect g a b) ∧
      TendstoInMeasure P (fun n ω => (g (mb n ω) - g (∫ x, z true x ⬝ᵥ
        leastSquaresFit (recordDesign z) recordResponse O n ω ∂Q.covLaw)) -
          unanchoredBalancedEstimate g φ t O mb n ω) atTop (fun _ => 0) := by
  obtain ⟨hW, hS, -⟩ := commonLimit_leastSquares_armMean hT hM hO hOm hlaw hφ hB hδ hmargin
    hvar true haff hX₂ ht hzQ hYQ hsi hov
  have hW' : IsConsistent (unanchoredBalancedEstimate g φ t O mb) (Q.marginalEffect g a b) P :=
    (hmb.comp_continuousAt hgb).sub (hW.comp_continuousAt hga)
  have hS' := (hmb.comp_continuousAt hgb).sub (hS.comp_continuousAt hga)
  exact ⟨hW', hS', tendstoInMeasure_sub_zero_of_same_limit hS' hW'⟩

/-- **The anchored comparisons on a link scale share their limit.** Under the hypotheses of
`commonLimit_leastSquares_armMean` for both arms, `true ↦ a` and `false ↦ c` (both regressions
affine in the features, both arms transported), with a reported contrast `d̂_bc` converging in
probability to the target marginal effect of `c` relative to `b`, and a link `g` continuous at
the target means of `a` and `c`, the weighted anchored comparison `anchoredBalancedEstimate` and
the standardized anchored comparison `linkMarginal g Q_X (z(true, ·)ᵀξ̂) (z(false, ·)ᵀξ̂) - d̂_bc`
both converge in probability to the target marginal effect of `b` relative to `a`, and their
difference converges in probability to `0`. -/
theorem commonLimit_leastSquares_anchored [IsProbabilityMeasure T.μ] [IsProbabilityMeasure P]
    [IsProbabilityMeasure Q.μ] (hT : T.IsRandomizedTwoArm) (hM : T.LinearOutcomeModel z ξ₀)
    (hO : IsIIDSample O P) (hOm : ∀ i, Measurable (O i)) (hlaw : P.map (O 0) = T.ipdLaw)
    (hφ : Measurable φ) {B : ℝ} (hB : ∀ x, ‖φ x - t‖ ≤ B) {δ : ℝ} (hδ : 0 < δ)
    (hmargin : ∀ v : Fin p → ℝ, ‖v‖ = 1 → δ ≤ T.covLaw.real {x | δ ≤ v ⬝ᵥ (φ x - t)})
    {σ2 : ℝ} (hvar : T.ipdLaw[fun o => (o.2.2 - z o.2.1 o.1 ⬝ᵥ ξ₀) ^ 2 |
      MeasurableSpace.comap (fun o : 𝒳 × Bool × ℝ => (o.1, o.2.1)) inferInstance]
        ≤ᵐ[T.ipdLaw] fun _ => σ2)
    {α : Bool → ℝ} {β : Bool → Fin p → ℝ} (haff : ∀ a x, z a x ⬝ᵥ ξ₀ = α a + β a ⬝ᵥ φ x)
    (hX₂ : Measurable Q.X) (ht : ∀ k, ∫ x, φ x k ∂Q.covLaw = t k)
    (hzQ : ∀ a j, Integrable (fun x => z a x j) Q.covLaw) {a b c : ι}
    (hYQa : Integrable (Q.Y a) Q.μ) (hYQc : Integrable (Q.Y c) Q.μ)
    (hsia : StructurallyInvariant T.μ T.X (T.Y true) Q.μ Q.X (Q.Y a))
    (hsic : StructurallyInvariant T.μ T.X (T.Y false) Q.μ Q.X (Q.Y c))
    (hov : Q.covLaw ≪ T.covLaw) {dbc : ℕ → Ξ → ℝ} {g : ℝ → ℝ}
    (hdbc : TendstoInMeasure P dbc atTop fun _ => Q.marginalEffect g b c)
    (hga : ContinuousAt g (Q.armMean a)) (hgc : ContinuousAt g (Q.armMean c)) :
    IsConsistent (anchoredBalancedEstimate g φ t O dbc) (Q.marginalEffect g a b) P ∧
      TendstoInMeasure P (fun n ω => linkMarginal g Q.covLaw
        (fun x => z true x ⬝ᵥ leastSquaresFit (recordDesign z) recordResponse O n ω)
        (fun x => z false x ⬝ᵥ leastSquaresFit (recordDesign z) recordResponse O n ω) -
          dbc n ω) atTop (fun _ => Q.marginalEffect g a b) ∧
      TendstoInMeasure P (fun n ω => (linkMarginal g Q.covLaw
        (fun x => z true x ⬝ᵥ leastSquaresFit (recordDesign z) recordResponse O n ω)
        (fun x => z false x ⬝ᵥ leastSquaresFit (recordDesign z) recordResponse O n ω) -
          dbc n ω) - anchoredBalancedEstimate g φ t O dbc n ω) atTop (fun _ => 0) := by
  obtain ⟨hA, -, -⟩ := commonLimit_leastSquares_armMean hT hM hO hOm hlaw hφ hB hδ hmargin
    hvar true (haff true) hX₂ ht (hzQ true) hYQa hsia hov
  obtain ⟨hC, -, -⟩ := commonLimit_leastSquares_armMean hT hM hO hOm hlaw hφ hB hδ hmargin
    hvar false (haff false) hX₂ ht (hzQ false) hYQc hsic hov
  have hlim : g (Q.armMean c) - g (Q.armMean a) - Q.marginalEffect g b c =
      Q.marginalEffect g a b := by
    simp only [Population.marginalEffect]; ring
  have hW : IsConsistent (anchoredBalancedEstimate g φ t O dbc) (Q.marginalEffect g a b) P := by
    have h := isConsistent_link_contrast hA hC hdbc hga hgc
    rw [hlim] at h
    exact h
  have hS := tendstoInMeasure_leastSquares_anchored hT hM hO hlaw hX₂ hYQa hYQc hsia hsic hov
    hzQ hdbc hga hgc
  exact ⟨hW, hS, tendstoInMeasure_sub_zero_of_same_limit hS hW⟩

/-- **The limit of the standardized contrast on the identity scale under relative constancy.**
In a randomized trial with a linear outcome model and design coordinates integrable under `Q_X`,
if the conditional contrast `z(false, ·)ᵀξ₀ - z(true, ·)ᵀξ₀` of the trial is the conditional mean
of `Y(c) - Y(a)` in the target (relative constancy on the identity scale; the arm regressions
themselves need not carry over), then the standardized contrast of the fit converges in
probability to `E_Q[Y(c)] - E_Q[Y(a)]`. -/
theorem tendstoInMeasure_leastSquares_contrast_identity [IsProbabilityMeasure T.μ]
    [IsFiniteMeasure Q.μ] [IsProbabilityMeasure P] (hT : T.IsRandomizedTwoArm)
    (hM : T.LinearOutcomeModel z ξ₀) (hO : IsIIDSample O P) (hlaw : P.map (O 0) = T.ipdLaw)
    (hX₂ : Measurable Q.X) {a c : ι} (hYQa : Integrable (Q.Y a) Q.μ)
    (hYQc : Integrable (Q.Y c) Q.μ)
    (hrel : (fun ω => z false (Q.X ω) ⬝ᵥ ξ₀ - z true (Q.X ω) ⬝ᵥ ξ₀) =ᵐ[Q.μ]
      Q.μ[fun ω => Q.Y c ω - Q.Y a ω | MeasurableSpace.comap Q.X inferInstance])
    (hzQ : ∀ a j, Integrable (fun x => z a x j) Q.covLaw) :
    TendstoInMeasure P (fun n ω => linkMarginal id Q.covLaw
        (fun x => z true x ⬝ᵥ leastSquaresFit (recordDesign z) recordResponse O n ω)
        (fun x => z false x ⬝ᵥ leastSquaresFit (recordDesign z) recordResponse O n ω))
      atTop (fun _ => Q.armMean c - Q.armMean a) := by
  have hθ := hM.tendstoInMeasure hT hO hlaw
  have hfit : ∀ e : Bool, TendstoInMeasure P (fun n ω => ∫ x, z e x ⬝ᵥ
      leastSquaresFit (recordDesign z) recordResponse O n ω ∂Q.covLaw) atTop
      (fun _ => ∫ x, z e x ⬝ᵥ ξ₀ ∂Q.covLaw) := fun e => by
    obtain ⟨hm, hH, hdom, hcont⟩ := linearSurface_dominated (hM.measurable_z e) (hzQ e) ξ₀
    exact tendstoInMeasure_integral_of_dominated (h := fun ξ x => z e x ⬝ᵥ ξ)
      (Eventually.of_forall hm) hH hdom hcont hθ
  have hi : ∀ e : Bool, Integrable (fun x => z e x ⬝ᵥ ξ₀) Q.covLaw := fun e => by
    simp only [dotProduct]
    exact integrable_finsetSum _ fun j _ => (hzQ e j).mul_const _
  have hid : ∫ ω, (Q.Y c ω - Q.Y a ω) ∂Q.μ =
      ∫ x, (z false x ⬝ᵥ ξ₀ - z true x ⬝ᵥ ξ₀) ∂Q.covLaw :=
    Transport.integral_eq_integral_map_of_condExp (Y := fun ω => Q.Y c ω - Q.Y a ω)
      (f := fun x => z false x ⬝ᵥ ξ₀ - z true x ⬝ᵥ ξ₀) hX₂ (hYQc.sub hYQa)
      ((measurable_linearSurface hM.measurable_z ξ₀ false).sub
        (measurable_linearSurface hM.measurable_z ξ₀ true)) hrel
  rw [integral_sub hYQc hYQa, integral_sub (hi false) (hi true)] at hid
  have h := (hfit false).sub (hfit true)
  simp only [Pi.sub_def] at h
  simp only [linkMarginal, id, Population.armMean]
  rw [hid]
  exact h

/-- **The anchored comparisons on the identity scale share their limit under relative constancy
only.** Under the hypotheses of `commonLimit_leastSquares_armMean` for both arms, except that
absolute constancy of the arms is replaced by relative constancy on the identity scale (the
conditional contrast `z(false, ·)ᵀξ₀ - z(true, ·)ᵀξ₀` of the trial is the conditional mean of
`Y(c) - Y(a)` in the target), with a reported contrast `d̂_bc` converging in probability to
`E_Q[Y(c)] - E_Q[Y(b)]`, the weighted and the standardized anchored comparisons on the identity
scale both converge in probability to `E_Q[Y(b)] - E_Q[Y(a)]`, and their difference converges
in probability to `0`. -/
theorem commonLimit_leastSquares_anchored_identity [IsProbabilityMeasure T.μ]
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q.μ] (hT : T.IsRandomizedTwoArm)
    (hM : T.LinearOutcomeModel z ξ₀) (hO : IsIIDSample O P) (hOm : ∀ i, Measurable (O i))
    (hlaw : P.map (O 0) = T.ipdLaw) (hφ : Measurable φ) {B : ℝ} (hB : ∀ x, ‖φ x - t‖ ≤ B)
    {δ : ℝ} (hδ : 0 < δ)
    (hmargin : ∀ v : Fin p → ℝ, ‖v‖ = 1 → δ ≤ T.covLaw.real {x | δ ≤ v ⬝ᵥ (φ x - t)})
    {σ2 : ℝ} (hvar : T.ipdLaw[fun o => (o.2.2 - z o.2.1 o.1 ⬝ᵥ ξ₀) ^ 2 |
      MeasurableSpace.comap (fun o : 𝒳 × Bool × ℝ => (o.1, o.2.1)) inferInstance]
        ≤ᵐ[T.ipdLaw] fun _ => σ2)
    {α : Bool → ℝ} {β : Bool → Fin p → ℝ} (haff : ∀ a x, z a x ⬝ᵥ ξ₀ = α a + β a ⬝ᵥ φ x)
    (hX₂ : Measurable Q.X) (ht : ∀ k, ∫ x, φ x k ∂Q.covLaw = t k)
    (hzQ : ∀ a j, Integrable (fun x => z a x j) Q.covLaw) {a b c : ι}
    (hYQa : Integrable (Q.Y a) Q.μ) (hYQc : Integrable (Q.Y c) Q.μ)
    (hrel : (fun ω => z false (Q.X ω) ⬝ᵥ ξ₀ - z true (Q.X ω) ⬝ᵥ ξ₀) =ᵐ[Q.μ]
      Q.μ[fun ω => Q.Y c ω - Q.Y a ω | MeasurableSpace.comap Q.X inferInstance])
    {dbc : ℕ → Ξ → ℝ} (hdbc : TendstoInMeasure P dbc atTop fun _ => Q.marginalEffect id b c) :
    IsConsistent (anchoredBalancedEstimate id φ t O dbc) (Q.marginalEffect id a b) P ∧
      TendstoInMeasure P (fun n ω => linkMarginal id Q.covLaw
        (fun x => z true x ⬝ᵥ leastSquaresFit (recordDesign z) recordResponse O n ω)
        (fun x => z false x ⬝ᵥ leastSquaresFit (recordDesign z) recordResponse O n ω) -
          dbc n ω) atTop (fun _ => Q.marginalEffect id a b) ∧
      TendstoInMeasure P (fun n ω => (linkMarginal id Q.covLaw
        (fun x => z true x ⬝ᵥ leastSquaresFit (recordDesign z) recordResponse O n ω)
        (fun x => z false x ⬝ᵥ leastSquaresFit (recordDesign z) recordResponse O n ω) -
          dbc n ω) - anchoredBalancedEstimate id φ t O dbc n ω) atTop (fun _ => 0) := by
  have hlim : Q.armMean c - Q.armMean a - Q.marginalEffect id b c = Q.marginalEffect id a b := by
    simp only [Population.marginalEffect, id]; ring
  have hS0 := tendstoInMeasure_leastSquares_contrast_identity hT hM hO hlaw hX₂ hYQa hYQc hrel
    hzQ
  have hS : TendstoInMeasure P (fun n ω => linkMarginal id Q.covLaw
        (fun x => z true x ⬝ᵥ leastSquaresFit (recordDesign z) recordResponse O n ω)
        (fun x => z false x ⬝ᵥ leastSquaresFit (recordDesign z) recordResponse O n ω) -
          dbc n ω) atTop (fun _ => Q.marginalEffect id a b) := by
    have h := hS0.sub hdbc
    simp only [Pi.sub_def, hlim] at h
    exact h
  -- the weighted comparison
  have hA := hM.isConsistent_balanced hT hO hOm hlaw hφ hB hδ hmargin hvar true (haff true)
  have hC := hM.isConsistent_balanced hT hO hOm hlaw hφ hB hδ hmargin hvar false (haff false)
  have h := isConsistent_link_contrast hA hC hdbc continuousAt_id continuousAt_id
  have hdiff : ∀ x, z false x ⬝ᵥ ξ₀ - z true x ⬝ᵥ ξ₀ =
      (α false - α true) + (β false - β true) ⬝ᵥ φ x := fun x => by
    rw [haff, haff, sub_dotProduct]; ring
  have hint := integral_affine_covLaw hφ hB ht hdiff
  have hid : ∫ ω, (Q.Y c ω - Q.Y a ω) ∂Q.μ =
      ∫ x, (z false x ⬝ᵥ ξ₀ - z true x ⬝ᵥ ξ₀) ∂Q.covLaw :=
    Transport.integral_eq_integral_map_of_condExp (Y := fun ω => Q.Y c ω - Q.Y a ω)
      (f := fun x => z false x ⬝ᵥ ξ₀ - z true x ⬝ᵥ ξ₀) hX₂ (hYQc.sub hYQa)
      ((measurable_linearSurface hM.measurable_z ξ₀ false).sub
        (measurable_linearSurface hM.measurable_z ξ₀ true)) hrel
  rw [integral_sub hYQc hYQa, hint] at hid
  have hval : id (α false + β false ⬝ᵥ t) - id (α true + β true ⬝ᵥ t) -
      Q.marginalEffect id b c = Q.marginalEffect id a b := by
    rw [← hlim]
    simp only [Population.armMean, id] at hid ⊢
    rw [sub_dotProduct] at hid
    linarith
  rw [hval] at h
  have hW : IsConsistent (anchoredBalancedEstimate id φ t O dbc) (Q.marginalEffect id a b) P := h
  exact ⟨hW, hS, tendstoInMeasure_sub_zero_of_same_limit hS hW⟩

end CommonLimit

/-! ### The final statements for the interaction design -/

section Primitive

variable {Ω₁ Ω₂ Ξ 𝒳 ι : Type*} [MeasurableSpace Ω₁] [MeasurableSpace Ω₂] [MeasurableSpace Ξ]
  [MeasurableSpace 𝒳] {p : ℕ} {T : Trial Ω₁ 𝒳 Bool} {Q : Population Ω₂ 𝒳 ι} {P : Measure Ξ}
  {O : ℕ → Ξ → 𝒳 × Bool × ℝ} {φ : 𝒳 → Fin p → ℝ} {t : Fin p → ℝ}
  {ξ₀ : Option (Fin p) ⊕ Option (Fin p) → ℝ}

/-- **Weighting and standardization share their limit, from primitive conditions.** Let `T` be
a randomized trial whose potential outcomes have finite second moments and whose regression is
linear in the interaction design of the features, `E[Y | X, A] = z(A, X)ᵀξ₀` with
`z(a, x) = (1, φ(x), 1[a], 1[a]φ(x))`; let `φ` be measurable with `‖φ(x) - t‖ ≤ B`, the margin
condition at `t` hold for the trial covariate law, and the conditional residual variance of the
records be bounded; let `O` be a measurable i.i.d. sample of the individual data. Let `Q` be a
target population with probability law, measurable covariates, feature means `t`, integrable
`Y(s)`, absolute constancy of arm `a` of the trial and treatment `s` of the target, and overlap.
Then the weighted arm mean and the standardized least squares fit both converge in probability
to `E_Q[Y(s)]`, and their difference converges in probability to `0`. -/
theorem commonLimit_interaction_armMean [IsProbabilityMeasure T.μ] [IsProbabilityMeasure P]
    [IsProbabilityMeasure Q.μ] (hT : T.IsRandomizedTwoArm) (hY2 : ∀ a, MemLp (T.Y a) 2 T.μ)
    (hφ : Measurable φ) {B : ℝ} (hB : ∀ x, ‖φ x - t‖ ≤ B) {δ : ℝ} (hδ : 0 < δ)
    (hmargin : ∀ v : Fin p → ℝ, ‖v‖ = 1 → δ ≤ T.covLaw.real {x | δ ≤ v ⬝ᵥ (φ x - t)})
    (hreg : IsOutcomeRegression T.μ T.A T.X T.obsOutcome
      fun a x => featureInteractionDesign φ a x ⬝ᵥ ξ₀)
    {σ2 : ℝ} (hvar : T.ipdLaw[fun o => (o.2.2 - featureInteractionDesign φ o.2.1 o.1 ⬝ᵥ ξ₀) ^ 2 |
      MeasurableSpace.comap (fun o : 𝒳 × Bool × ℝ => (o.1, o.2.1)) inferInstance]
        ≤ᵐ[T.ipdLaw] fun _ => σ2)
    (hO : IsIIDSample O P) (hOm : ∀ i, Measurable (O i)) (hlaw : P.map (O 0) = T.ipdLaw)
    (hX₂ : Measurable Q.X) (ht : ∀ k, ∫ x, φ x k ∂Q.covLaw = t k) (a : Bool) {s : ι}
    (hYQ : Integrable (Q.Y s) Q.μ)
    (hsi : StructurallyInvariant T.μ T.X (T.Y a) Q.μ Q.X (Q.Y s)) (hov : Q.covLaw ≪ T.covLaw) :
    IsConsistent (sampleBalancedArmMean φ t O a) (Q.armMean s) P ∧
      TendstoInMeasure P (fun n ω => ∫ x, featureInteractionDesign φ a x ⬝ᵥ
        leastSquaresFit (recordDesign (featureInteractionDesign φ)) recordResponse O n ω
          ∂Q.covLaw) atTop (fun _ => Q.armMean s) ∧
      TendstoInMeasure P (fun n ω => ∫ x, featureInteractionDesign φ a x ⬝ᵥ
        leastSquaresFit (recordDesign (featureInteractionDesign φ)) recordResponse O n ω
          ∂Q.covLaw - sampleBalancedArmMean φ t O a n ω) atTop (fun _ => 0) := by
  have : IsProbabilityMeasure Q.covLaw := Q.isProbabilityMeasure_covLaw hX₂
  exact commonLimit_leastSquares_armMean hT
    (T.linearOutcomeModel_featureInteraction hT hY2 hφ hB hδ hmargin hreg) hO hOm hlaw hφ hB
    hδ hmargin hvar a (featureInteractionDesign_dotProduct φ a · ξ₀) hX₂ ht
    (integrable_featureInteractionDesign hφ hB a) hYQ hsi hov

end Primitive

end PopulationAdjustment

end CausalInference
