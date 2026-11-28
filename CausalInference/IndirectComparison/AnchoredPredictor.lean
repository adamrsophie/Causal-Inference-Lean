/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.IndirectComparison.Basic
public import CausalInference.Measures.EffectModifier
public import CausalInference.Measures.LinkScaleExamples

/-!
# The anchored linear predictor and the shared effect modifier assumption

A network meta regression on the link `g` with mean function `g⁻¹` on the mean space `D` gives
treatment `t` the linear predictor

`η_t(x) = α + xᵀβ₁ + (γ_t + xᵀβ₂,t)`

(`anchoredPredictor`, `AnchoredModel.predictor`): prognostic effects `β₁` common to the arms, a
relative effect `γ_t` and treatment by covariate interactions `β₂,t`; the reference arm has
`γ = 0` and `β₂ = 0`, and the predictor is `interactionPredictor` of `Measures/EffectModifier.lean`
(`anchoredPredictor_eq_interactionPredictor`). The arm means are `g⁻¹ ∘ η_t`.

The **shared effect modifier assumption** for a set `S` of active treatments is that they have
the same interactions: `β₂,b = β₂,c` for `b, c ∈ S` (`SharedEffectModifiers`). Then the
predictor contrast of `b` against `c` is the constant `γ_b - γ_c` (`predictor_sub_of_shared`),
so on a scale `h` aligned with the model (`Transport.IsAlignedScale`) the conditional effect is
`γ_b - γ_c` at every covariate value and the average conditional effect is `γ_b - γ_c` in every
population (`linkConditional_eq_of_shared`). The marginal effect transports when the scale is
also collapsible (`linkMarginal_eq_of_shared`): for the identity link (mean or risk
difference, `linkMarginal_id_eq_of_shared`) and the log link (log risk ratio,
`linkMarginal_log_eq_of_shared`).

**The guarantee is collapsibility.** Over all anchored models with shared effect modifiers, the
marginal effect is the same in every two admissible covariate laws exactly when the scale is
collapsible (`universalTransport_iff_linkCollapsible`). On the logit scale it fails
(`not_universalTransport_logit`), with an explicit model: risks `σ(±1)` and `σ(1/2)`, `σ(5/2)` in
two equally likely strata, a conditional log odds ratio `3/2` everywhere, and a marginal log odds
ratio strictly below `3/2` (`logit_marginal_not_transported`). Reported as a risk difference, a
logit model transports neither the conditional nor the marginal effect
(`riskDifference_not_transported_of_logit`).

## Main definitions

* `anchoredPredictor`, `AnchoredModel`, `AnchoredModel.predictor`, `SharedEffectModifiers`.
* `AnchoredAdmissible`, `UniversalTransport`.

## Main results

* `predictor_sub_of_shared`, `linkConditional_eq_of_shared`, `linkMarginal_eq_of_shared`,
  `linkMarginal_id_eq_of_shared`, `linkMarginal_log_eq_of_shared`.
* `universalTransport_iff_linkCollapsible`, `universalTransport_id`, `universalTransport_log`,
  `not_universalTransport_logit`, `logit_marginal_not_transported`,
  `riskDifference_not_transported_of_logit`, `sharedExampleModel_transport`.

## References

* D. M. Phillippo, A. E. Ades, S. Dias, S. Palmer, K. R. Abrams and N. J. Welton, *Methods for
  population-adjusted indirect comparisons in health technology appraisal*, Medical Decision
  Making 38 (2018).
* D. M. Phillippo, S. Dias, A. E. Ades, M. Belger, A. Brnabic, A. Schacht, D. Saure, Z. Kadziola
  and N. J. Welton, *Multilevel network meta-regression for population-adjusted treatment
  comparisons*, Journal of the Royal Statistical Society Series A 183 (2020).
-/

@[expose] public section

namespace CausalInference

namespace IndirectComparison

open MeasureTheory ProbabilityTheory EffectMeasure Transport

variable {p : ℕ}

/-! ### The predictor and the assumption -/

/-- The **anchored linear predictor** `α + xᵀβ₁ + (γ + xᵀβ₂)` of an arm with relative effect `γ`
and interactions `β₂`. -/
def anchoredPredictor (α : ℝ) (β₁ : Fin p → ℝ) (γ : ℝ) (β₂ : Fin p → ℝ) (x : Fin p → ℝ) : ℝ :=
  α + ∑ j, x j * β₁ j + (γ + ∑ j, x j * β₂ j)

/-- The anchored predictor is the active arm of `interactionPredictor`, and with `γ = 0`,
`β₂ = 0` its reference arm. -/
theorem anchoredPredictor_eq_interactionPredictor (α γ : ℝ) (β₁ β₂ x : Fin p → ℝ) :
    anchoredPredictor α β₁ γ β₂ x = interactionPredictor α γ β₁ β₂ true x ∧
      anchoredPredictor α β₁ 0 0 x = interactionPredictor α γ β₁ β₂ false x := by
  simp [anchoredPredictor, interactionPredictor]

/-- The predictor contrast of two arms with the same interactions is the difference of their
relative effects. -/
theorem anchoredPredictor_sub (α : ℝ) (β₁ : Fin p → ℝ) (γb γc : ℝ) (β₂ x : Fin p → ℝ) :
    anchoredPredictor α β₁ γb β₂ x - anchoredPredictor α β₁ γc β₂ x = γb - γc := by
  simp only [anchoredPredictor]; ring

/-- An **anchored model** on `p` covariates for the treatments `ι`: common intercept `α` and
prognostic effects `β₁`, and for each treatment a relative effect `γ t` and interactions
`β₂ t`. -/
structure AnchoredModel (ι : Type*) (p : ℕ) where
  /-- The intercept. -/
  α : ℝ
  /-- The prognostic effects, common to the arms. -/
  β₁ : Fin p → ℝ
  /-- The relative effects. -/
  γ : ι → ℝ
  /-- The treatment by covariate interactions. -/
  β₂ : ι → Fin p → ℝ

namespace AnchoredModel

variable {ι : Type*}

/-- The linear predictor of treatment `t`. -/
def predictor (M : AnchoredModel ι p) (t : ι) (x : Fin p → ℝ) : ℝ :=
  anchoredPredictor M.α M.β₁ (M.γ t) (M.β₂ t) x

/-- The model is **anchored at** the reference treatment `r`: `γ r = 0` and `β₂ r = 0`. -/
def IsAnchoredAt (M : AnchoredModel ι p) (r : ι) : Prop := M.γ r = 0 ∧ M.β₂ r = 0

/-- The treatments in `S` **share their effect modifiers**: they have the same treatment by
covariate interactions. -/
def SharedEffectModifiers (M : AnchoredModel ι p) (S : Set ι) : Prop :=
  ∀ b ∈ S, ∀ c ∈ S, M.β₂ b = M.β₂ c

/-- **Under shared effect modifiers the predictor contrast is constant**:
`η_b(x) - η_c(x) = γ_b - γ_c` for `b, c ∈ S`. -/
theorem predictor_sub_of_shared {M : AnchoredModel ι p} {S : Set ι}
    (h : M.SharedEffectModifiers S) {b c : ι} (hb : b ∈ S) (hc : c ∈ S) (x : Fin p → ℝ) :
    M.predictor b x - M.predictor c x = M.γ b - M.γ c := by
  rw [predictor, predictor, h b hb c hc, anchoredPredictor_sub]

/-- In a model anchored at `r` the conditional effect of `t` against `r` on the model scale is
`γ_t + xᵀβ₂,t`, the interaction model of `Measures/EffectModifier.lean`. -/
theorem linkContrast_of_isAnchoredAt {M : AnchoredModel ι p} {r : ι} (hr : M.IsAnchoredAt r)
    {g : ℝ → ℝ} {m : ι → (Fin p → ℝ) → ℝ} (hm : ∀ t x, g (m t x) = M.predictor t x) (t : ι)
    (x : Fin p → ℝ) : linkContrast g (m r) (m t) x = M.γ t + ∑ j, x j * M.β₂ t j := by
  simp only [linkContrast, hm, predictor, anchoredPredictor, hr.1, hr.2]
  simp

end AnchoredModel

/-! ### Transport under shared effect modifiers -/

section Transport

variable {ι : Type*} {D : Set ℝ} {g ginv : ℝ → ℝ} {M : AnchoredModel ι p} {S : Set ι}
  {b c : ι}

/-- **Conditional transport under shared effect modifiers.** If the reported scale `h` is
aligned with the model and `b, c` share their effect modifiers, then in every covariate law `P`
under which both predictors lie almost surely in `g(D)`, the average conditional effect of `b`
against `c` on the scale `h` is `γ_b - γ_c`. No collapsibility is needed. -/
theorem linkConditional_eq_of_shared {h : ℝ → ℝ} (hal : IsAlignedScale D g ginv h)
    (hS : M.SharedEffectModifiers S) (hb : b ∈ S) (hc : c ∈ S) (P : Measure (Fin p → ℝ))
    [IsProbabilityMeasure P] (hP : ∀ᵐ x ∂P, M.predictor b x ∈ g '' D ∧ M.predictor c x ∈ g '' D) :
    linkConditional h P (fun x => ginv (M.predictor c x)) (fun x => ginv (M.predictor b x)) =
      M.γ b - M.γ c :=
  linkConditional_eq_of_aligned hal (AnchoredModel.predictor_sub_of_shared hS hb hc) P hP

/-- **Marginal transport on a collapsible scale under shared effect modifiers.** If the model
scale is collapsible on `D`, `g⁻¹` inverts `g` on `D`, `b, c` share their effect modifiers, and
under `P` the predictors lie almost surely in `g(D)` with integrable means, the marginal effect of
`b` against `c` is `γ_b - γ_c`, whatever `P`. -/
theorem linkMarginal_eq_of_shared (hcol : LinkCollapsible D g) (hinv : ∀ q ∈ D, ginv (g q) = q)
    (hS : M.SharedEffectModifiers S) (hb : b ∈ S) (hc : c ∈ S) (P : Measure (Fin p → ℝ))
    [IsProbabilityMeasure P] (hP : ∀ᵐ x ∂P, M.predictor b x ∈ g '' D ∧ M.predictor c x ∈ g '' D)
    (hib : Integrable (fun x => ginv (M.predictor b x)) P)
    (hic : Integrable (fun x => ginv (M.predictor c x)) P) :
    linkMarginal g P (fun x => ginv (M.predictor c x)) (fun x => ginv (M.predictor b x)) =
      M.γ b - M.γ c :=
  linkMarginal_eq_of_aligned hcol hinv (AnchoredModel.predictor_sub_of_shared hS hb hc) P hP
    hib hic

/-- **The mean difference transports under shared effect modifiers**: on the identity link the
marginal effect of `b` against `c` is `γ_b - γ_c` in every covariate law with integrable
predictors. -/
theorem linkMarginal_id_eq_of_shared (hS : M.SharedEffectModifiers S) (hb : b ∈ S) (hc : c ∈ S)
    (P : Measure (Fin p → ℝ)) [IsProbabilityMeasure P] (hib : Integrable (M.predictor b) P)
    (hic : Integrable (M.predictor c) P) :
    linkMarginal id P (M.predictor c) (M.predictor b) = M.γ b - M.γ c :=
  linkMarginal_eq_of_shared (D := Set.univ) (ginv := id) linkCollapsible_id (fun _ _ => rfl) hS
    hb hc P (Filter.Eventually.of_forall fun _ => ⟨⟨_, trivial, rfl⟩, ⟨_, trivial, rfl⟩⟩) hib hic

/-- **The log risk ratio transports under shared effect modifiers**: on the log link, with means
`exp ∘ η`, the marginal log risk ratio of `b` against `c` is `γ_b - γ_c` in every covariate law
with integrable means. -/
theorem linkMarginal_log_eq_of_shared (hS : M.SharedEffectModifiers S) (hb : b ∈ S)
    (hc : c ∈ S) (P : Measure (Fin p → ℝ)) [IsProbabilityMeasure P]
    (hib : Integrable (fun x => Real.exp (M.predictor b x)) P)
    (hic : Integrable (fun x => Real.exp (M.predictor c x)) P) :
    linkMarginal Real.log P (fun x => Real.exp (M.predictor c x))
        (fun x => Real.exp (M.predictor b x)) = M.γ b - M.γ c := by
  have hall : ∀ t : ℝ, t ∈ Real.log '' Set.Ioi 0 := fun t =>
    ⟨Real.exp t, Real.exp_pos t, Real.log_exp t⟩
  exact linkMarginal_eq_of_shared linkCollapsible_log (fun q hq => Real.exp_log hq) hS hb hc P
    (Filter.Eventually.of_forall fun x => ⟨hall _, hall _⟩) hib hic

end Transport

/-! ### The universal guarantee is collapsibility -/

section Universal

variable {D : Set ℝ} {g ginv : ℝ → ℝ}

/-- A covariate law `P` is **admissible** for two arms with predictors
`η_b = anchoredPredictor α β₁ γb β₂` and `η_c = anchoredPredictor α β₁ γc β₂` on the link `g`
with mean function `ginv`: both predictors lie almost surely in `g(D)` and both means are
integrable. -/
def AnchoredAdmissible (D : Set ℝ) (g ginv : ℝ → ℝ) (α : ℝ) (β₁ : Fin p → ℝ) (γb γc : ℝ)
    (β₂ : Fin p → ℝ) (P : Measure (Fin p → ℝ)) : Prop :=
  (∀ᵐ x ∂P, anchoredPredictor α β₁ γb β₂ x ∈ g '' D ∧ anchoredPredictor α β₁ γc β₂ x ∈ g '' D) ∧
    Integrable (fun x => ginv (anchoredPredictor α β₁ γb β₂ x)) P ∧
    Integrable (fun x => ginv (anchoredPredictor α β₁ γc β₂ x)) P

/-- The **universal transport guarantee** for the link `g` with mean function `ginv` on `D`: for
every anchored pair of arms with shared effect modifiers, on any number of covariates, the
marginal effect on the scale `g` is the same in every two admissible covariate laws. -/
def UniversalTransport (D : Set ℝ) (g ginv : ℝ → ℝ) : Prop :=
  ∀ (p : ℕ) (α : ℝ) (β₁ : Fin p → ℝ) (γb γc : ℝ) (β₂ : Fin p → ℝ)
    (P Q : Measure (Fin p → ℝ)) [IsProbabilityMeasure P] [IsProbabilityMeasure Q],
    AnchoredAdmissible D g ginv α β₁ γb γc β₂ P → AnchoredAdmissible D g ginv α β₁ γb γc β₂ Q →
    linkMarginal g P (fun x => ginv (anchoredPredictor α β₁ γc β₂ x))
        (fun x => ginv (anchoredPredictor α β₁ γb β₂ x)) =
      linkMarginal g Q (fun x => ginv (anchoredPredictor α β₁ γc β₂ x))
        (fun x => ginv (anchoredPredictor α β₁ γb β₂ x))

/-- The scalar predictor `x₀ + γ`. -/
theorem anchoredPredictor_scalar (γ : ℝ) (x : Fin 1 → ℝ) :
    anchoredPredictor 0 (fun _ => 1) γ 0 x = x 0 + γ := by
  simp [anchoredPredictor]

/-- **A universal transport guarantee is equivalent to collapsibility.** For a measurable link
`g` with a measurable mean function `ginv` inverting it on `D`, and a measurable range `g(D)`,
the marginal effect of every anchored pair with shared effect modifiers is the same in all
admissible covariate laws if and only if the effect measure is collapsible on the scale `g`.
A constant conditional effect `c` of means `a, b` is the scalar model `η_c(u) = u`,
`η_b(u) = u + c` under the law of `u = g(a(X))`; comparing it with a point mass gives `c`. -/
theorem universalTransport_iff_linkCollapsible (hinv : ∀ q ∈ D, ginv (g q) = q)
    (hg : Measurable g) (hginv : Measurable ginv) (hD : MeasurableSet (g '' D)) :
    UniversalTransport D g ginv ↔ LinkCollapsible D g := by
  constructor
  · intro hU X _ ν _ a b ha hb hDab c hc
    have hgm : AEMeasurable (fun x => g (a x)) ν := hg.comp_aemeasurable ha.aemeasurable
    set u : X → Fin 1 → ℝ := fun x _ => g (a x)
    have hu : AEMeasurable u ν := AEMeasurable.of_eval (fun _ => hgm)
    have hrel1 : ∀ᵐ x ∂ν, ginv (g (a x) + c) = b x := by
      filter_upwards [hDab, hc] with x hx hcx
      simp only [linkContrast] at hcx
      rw [← hcx, add_sub_cancel, hinv _ hx.2]
    have hrel0 : ∀ᵐ x ∂ν, ginv (g (a x) + 0) = a x := by
      filter_upwards [hDab] with x hx
      rw [add_zero, hinv _ hx.1]
    have hev : ∀ γ : ℝ, Measurable fun y : Fin 1 → ℝ => y 0 + γ := fun γ => by fun_prop
    have hmeas : ∀ γ : ℝ, Measurable fun y : Fin 1 → ℝ => ginv (y 0 + γ) :=
      fun γ => hginv.comp (hev γ)
    have hset : ∀ γ : ℝ, MeasurableSet {y : Fin 1 → ℝ | y 0 + γ ∈ g '' D} := fun γ => hev γ hD
    have hP : AnchoredAdmissible D g ginv 0 (fun _ => 1) c 0 0 (ν.map u) := by
      simp only [AnchoredAdmissible, anchoredPredictor_scalar]
      refine ⟨(ae_map_iff hu ((hset c).inter (hset 0))).2 ?_, ?_, ?_⟩
      · filter_upwards [hDab, hc] with x hx hcx
        simp only [linkContrast] at hcx
        exact ⟨⟨b x, hx.2, by simp only [u]; linarith⟩, ⟨a x, hx.1, by simp [u]⟩⟩
      · rw [integrable_map_measure (hmeas c).aestronglyMeasurable hu]
        exact (integrable_congr hrel1).2 hb
      · rw [integrable_map_measure (hmeas 0).aestronglyMeasurable hu]
        exact (integrable_congr hrel0).2 ha
    have : IsProbabilityMeasure (ν.map u) := (Measure.isProbabilityMeasure_map_iff hu).2 ‹_›
    obtain ⟨x₀, hx₀, hcx₀⟩ := (hDab.and hc).exists
    simp only [linkContrast] at hcx₀
    set y₀ : Fin 1 → ℝ := fun _ => g (a x₀)
    have hQ : AnchoredAdmissible D g ginv 0 (fun _ => 1) c 0 0 (Measure.dirac y₀) := by
      refine ⟨?_, integrable_dirac (by simp), integrable_dirac (by simp)⟩
      rw [ae_dirac_eq]
      simp only [anchoredPredictor_scalar, Filter.eventually_pure]
      exact ⟨⟨b x₀, hx₀.2, by simp only [y₀]; linarith⟩, ⟨a x₀, hx₀.1, by simp [y₀]⟩⟩
    have key := hU 1 0 (fun _ => 1) c 0 0 (ν.map u) (Measure.dirac y₀) hP hQ
    simp only [linkMarginal, anchoredPredictor_scalar, integral_dirac] at key
    rw [integral_map hu (hmeas c).aestronglyMeasurable,
      integral_map hu (hmeas 0).aestronglyMeasurable,
      integral_congr_ae hrel1, integral_congr_ae hrel0] at key
    rw [linkMarginal, key]
    simp only [y₀, add_zero, hinv _ hx₀.1]
    rw [show g (a x₀) + c = g (b x₀) by linarith, hinv _ hx₀.2]
    linarith
  · intro hC p α β₁ γb γc β₂ P Q _ _ hP hQ
    rw [linkMarginal_eq_of_aligned hC hinv (anchoredPredictor_sub α β₁ γb γc β₂) P hP.1 hP.2.1
        hP.2.2,
      linkMarginal_eq_of_aligned hC hinv (anchoredPredictor_sub α β₁ γb γc β₂) Q hQ.1 hQ.2.1
        hQ.2.2]

/-- **The identity link has the universal guarantee.** -/
theorem universalTransport_id : UniversalTransport Set.univ id id :=
  (universalTransport_iff_linkCollapsible (fun _ _ => rfl) measurable_id measurable_id
    (by simp)).2 linkCollapsible_id

/-- **The log link has the universal guarantee.** -/
theorem universalTransport_log : UniversalTransport (Set.Ioi 0) Real.log Real.exp :=
  (universalTransport_iff_linkCollapsible (fun _ hq => Real.exp_log hq) Real.measurable_log
    Real.measurable_exp (by
      convert MeasurableSet.univ
      exact Set.eq_univ_of_forall fun t => ⟨Real.exp t, Real.exp_pos t, Real.log_exp t⟩)).2
    linkCollapsible_log

/-- The logit is measurable. -/
theorem measurable_logit : Measurable logit := by
  unfold logit odds; fun_prop

/-- Every real number is a logit of a probability. -/
theorem logit_image_Ioo : logit '' Set.Ioo 0 1 = Set.univ :=
  Set.eq_univ_of_forall fun t => ⟨Real.sigmoid t, sigmoid_mem_Ioo t, logit_sigmoid t⟩

/-- **The logit link does not have the universal guarantee**: shared effect modifiers do not
make the marginal log odds ratio transportable. -/
theorem not_universalTransport_logit : ¬ UniversalTransport (Set.Ioo 0 1) logit Real.sigmoid :=
  fun h => not_linkCollapsible_logit ((universalTransport_iff_linkCollapsible
    (fun q (hq : q ∈ Set.Ioo 0 1) => sigmoid_logit hq.1 hq.2) measurable_logit
    continuous_sigmoid.measurable (by rw [logit_image_Ioo]; exact MeasurableSet.univ)).1 h)

end Universal

/-! ### Explicit models on the logit scale -/

section Logit

/-- The covariate value `±1` of a binary stratifier. -/
def signCov (v : Bool) : Fin 1 → ℝ := fun _ => if v then 1 else -1

/-- The law of `signCov` under two equally likely strata. -/
noncomputable def signLaw : Measure (Fin 1 → ℝ) := halfLaw.map signCov

instance : IsProbabilityMeasure signLaw :=
  (Measure.isProbabilityMeasure_map_iff (measurable_of_finite signCov).aemeasurable).2
    inferInstance

/-- The mean under `signLaw` of a measurable function is its average at `±1`. -/
theorem integral_signLaw {f : (Fin 1 → ℝ) → ℝ} (hf : Measurable f) :
    ∫ x, f x ∂signLaw = (f (signCov true) + f (signCov false)) / 2 := by
  rw [signLaw, integral_map (measurable_of_finite signCov).aemeasurable hf.aestronglyMeasurable,
    integral_halfLaw]

/-- The reference risk `σ(η_c(x))` of the logit model with `η_c(x) = x`. -/
noncomputable def logitRefRisk (x : Fin 1 → ℝ) : ℝ :=
  Real.sigmoid (anchoredPredictor 0 (fun _ => 1) 0 0 x)

/-- The active risk `σ(η_b(x))` of the logit model with `η_b(x) = x + 3/2`. -/
noncomputable def logitActRisk (x : Fin 1 → ℝ) : ℝ :=
  Real.sigmoid (anchoredPredictor 0 (fun _ => 1) (3 / 2) 0 x)

theorem measurable_logitRefRisk : Measurable logitRefRisk := by
  unfold logitRefRisk anchoredPredictor; fun_prop

theorem measurable_logitActRisk : Measurable logitActRisk := by
  unfold logitActRisk anchoredPredictor; fun_prop

/-- On the strata the two risks are the risks of `logisticRef` and `logisticAct`. -/
theorem logitRisk_signCov (v : Bool) :
    logitRefRisk (signCov v) = logisticRef v ∧ logitActRisk (signCov v) = logisticAct v := by
  cases v <;> norm_num [logitRefRisk, logitActRisk, anchoredPredictor, signCov, logisticRef,
    logisticAct]

/-- **The marginal log odds ratio is not transported under shared effect modifiers.** In the
logit model `η_c(x) = x`, `η_b(x) = x + 3/2` (no interactions, so the shared effect modifier
assumption holds trivially), the conditional log odds ratio of `b` against `c` is `3/2` at every
covariate value. With the strata `x = ±1` equally likely, the risks are `σ(1), σ(-1)` under `c`
(marginal risk `1/2`) and `σ(5/2), σ(1/2)` under `b`, and the marginal log odds ratio lies
strictly between `0` and `3/2`; in the population concentrated at `x = 1` it is `3/2`. -/
theorem logit_marginal_not_transported :
    (∀ x, linkContrast logit logitRefRisk logitActRisk x = 3 / 2) ∧
    ∫ x, logitRefRisk x ∂signLaw = 1 / 2 ∧
    0 < linkMarginal logit signLaw logitRefRisk logitActRisk ∧
    linkMarginal logit signLaw logitRefRisk logitActRisk < 3 / 2 ∧
    linkMarginal logit (Measure.dirac (signCov true)) logitRefRisk logitActRisk = 3 / 2 := by
  have hcon : ∀ x, linkContrast logit logitRefRisk logitActRisk x = 3 / 2 := fun x => by
    simp only [linkContrast, logitRefRisk, logitActRisk, logit_sigmoid, anchoredPredictor]
    ring
  have heq : linkMarginal logit signLaw logitRefRisk logitActRisk =
      linkMarginal logit halfLaw logisticRef logisticAct := by
    simp only [linkMarginal, integral_signLaw measurable_logitRefRisk,
      integral_signLaw measurable_logitActRisk, integral_halfLaw, (logitRisk_signCov _).1,
      (logitRisk_signCov _).2]
  have href : ∫ x, logitRefRisk x ∂signLaw = 1 / 2 := by
    rw [integral_signLaw measurable_logitRefRisk, (logitRisk_signCov _).1,
      (logitRisk_signCov _).1, ← integral_halfLaw, logisticExample_integral_ref]
  refine ⟨hcon, href, heq ▸ logisticExample_bounds.1, heq ▸ logisticExample_bounds.2, ?_⟩
  simpa [linkMarginal, integral_dirac, linkContrast] using hcon (signCov true)

/-- The risk difference of the logit model `η_b = η_c + 2` differs between `x = 0` and
`x = -1`: `σ(2) - σ(0) ≠ σ(1) - σ(-1)`. With `r = e`, equality would force `(r - 1)^3 = 0`. -/
theorem sigmoid_sub_ne : Real.sigmoid 2 - Real.sigmoid 0 ≠ Real.sigmoid 1 - Real.sigmoid (-1) := by
  rw [sigmoid_eq_exp_div, sigmoid_eq_exp_div, sigmoid_eq_exp_div, sigmoid_eq_exp_div,
    Real.exp_zero, Real.exp_neg, show (2 : ℝ) = 1 + 1 by norm_num, Real.exp_add]
  have hr : 1 < Real.exp 1 := by linarith [Real.add_one_lt_exp (x := (1 : ℝ)) one_ne_zero]
  set r := Real.exp 1
  have hr0 : 0 < r := by linarith
  intro h
  field_simp at h
  nlinarith [pow_pos (sub_pos.2 hr) 3, hr0]

/-- **Reported as a risk difference, a logit model transports neither effect.** In the logit
model `η_c(x) = x`, `η_b(x) = x + 2` (no interactions), the conditional risk difference of `b`
against `c` and the marginal risk difference both differ between the populations concentrated
at `x = 0` and at `x = -1`, although the conditional log odds ratio is `2` in both. -/
theorem riskDifference_not_transported_of_logit :
    let mc : (Fin 1 → ℝ) → ℝ := fun x => Real.sigmoid (anchoredPredictor 0 (fun _ => 1) 0 0 x)
    let mb : (Fin 1 → ℝ) → ℝ := fun x => Real.sigmoid (anchoredPredictor 0 (fun _ => 1) 2 0 x)
    (∀ x, linkContrast logit mc mb x = 2) ∧
      linkConditional id (Measure.dirac fun _ => 0) mc mb ≠
        linkConditional id (Measure.dirac fun _ => -1) mc mb ∧
      linkMarginal id (Measure.dirac fun _ => 0) mc mb ≠
        linkMarginal id (Measure.dirac fun _ => -1) mc mb := by
  intro mc mb
  have hne : Real.sigmoid 2 - Real.sigmoid 0 ≠ Real.sigmoid (-1 + 2) - Real.sigmoid (-1) := by
    rw [show (-1 : ℝ) + 2 = 1 by norm_num]; exact sigmoid_sub_ne
  refine ⟨fun x => ?_, ?_, ?_⟩
  · simp only [linkContrast, mc, mb, logit_sigmoid, anchoredPredictor]; ring
  · simpa [linkConditional, integral_dirac, linkContrast, mc, mb, anchoredPredictor] using hne
  · simpa [linkMarginal, integral_dirac, mc, mb, anchoredPredictor] using hne

end Logit

/-! ### An anchored model with shared effect modifiers -/

/-- The anchored model on one covariate for the treatments `0, 1, 2`: intercept `0`, prognostic
effect `1`, relative effects `γ = (0, 1, 3)` and interactions `β₂ = (0, 2, 2)`, so the reference
`0` has no effect and `1`, `2` share their effect modifiers. -/
def sharedExampleModel : AnchoredModel (Fin 3) 1 :=
  ⟨0, fun _ => 1, ![0, 1, 3], ![0, fun _ => 2, fun _ => 2]⟩

/-- **An instance of transport under shared effect modifiers.** In `sharedExampleModel` the model
is anchored at `0` and the treatments `{1, 2}` share their effect modifiers. The conditional
effect of `1` against `0` is `1 + 2x`, which varies with `x`; the predictor contrast of `2`
against `1` is `2` everywhere; and the mean difference, the average conditional effect on the
identity scale, and the marginal log risk ratio (means `exp ∘ η`) of `2` against `1` are all `2`
under the two strata `x = ±1`. -/
theorem sharedExampleModel_transport :
    sharedExampleModel.IsAnchoredAt 0 ∧ sharedExampleModel.SharedEffectModifiers {1, 2} ∧
      (∀ x, linkContrast id (sharedExampleModel.predictor 0) (sharedExampleModel.predictor 1) x =
        1 + 2 * x 0) ∧
      (∀ x, sharedExampleModel.predictor 2 x - sharedExampleModel.predictor 1 x = 2) ∧
      linkMarginal id signLaw (sharedExampleModel.predictor 1) (sharedExampleModel.predictor 2) =
        2 ∧
      linkConditional id signLaw (fun x => id (sharedExampleModel.predictor 1 x))
        (fun x => id (sharedExampleModel.predictor 2 x)) = 2 ∧
      linkMarginal Real.log signLaw (fun x => Real.exp (sharedExampleModel.predictor 1 x))
        (fun x => Real.exp (sharedExampleModel.predictor 2 x)) = 2 := by
  have hA : sharedExampleModel.IsAnchoredAt 0 := ⟨rfl, rfl⟩
  have hS : sharedExampleModel.SharedEffectModifiers {1, 2} := by
    intro b hb c hc
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hb hc
    rcases hb with rfl | rfl <;> rcases hc with rfl | rfl <;> rfl
  have h1 : (1 : Fin 3) ∈ ({1, 2} : Set (Fin 3)) := by simp
  have h2 : (2 : Fin 3) ∈ ({1, 2} : Set (Fin 3)) := by simp
  have hγ : sharedExampleModel.γ 2 - sharedExampleModel.γ 1 = 2 := by
    simp [sharedExampleModel]; norm_num
  have hm : ∀ t, Measurable (sharedExampleModel.predictor t) := fun t => by
    unfold AnchoredModel.predictor anchoredPredictor; fun_prop
  have hint : ∀ {φ : (Fin 1 → ℝ) → ℝ}, Measurable φ → Integrable φ signLaw := fun hφ =>
    (integrable_map_measure hφ.aestronglyMeasurable
      (measurable_of_finite signCov).aemeasurable).2 Integrable.of_finite
  refine ⟨hA, hS, fun x => ?_, fun x => ?_, ?_, ?_, ?_⟩
  · rw [AnchoredModel.linkContrast_of_isAnchoredAt hA (g := id) (m := sharedExampleModel.predictor)
      (fun _ _ => rfl)]
    simp [sharedExampleModel]; ring
  · rw [AnchoredModel.predictor_sub_of_shared hS h2 h1, hγ]
  · rw [linkMarginal_id_eq_of_shared hS h2 h1 signLaw (hint (hm 2)) (hint (hm 1)), hγ]
  · rw [linkConditional_eq_of_shared (D := Set.univ) (g := id) (ginv := id)
      (fun _ _ => rfl) hS h2 h1 signLaw
      (Filter.Eventually.of_forall fun _ => ⟨⟨_, trivial, rfl⟩, ⟨_, trivial, rfl⟩⟩), hγ]
  · rw [linkMarginal_log_eq_of_shared hS h2 h1 signLaw
      (hint (Real.measurable_exp.comp (hm 2))) (hint (Real.measurable_exp.comp (hm 1))), hγ]

end IndirectComparison

end CausalInference
