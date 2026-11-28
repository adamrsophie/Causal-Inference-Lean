/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.NetworkMetaRegression.Model
public import CausalInference.PartialIdentification.IdentifiedSet

/-!
# Estimands of multilevel network meta-regression in a target population

A target population has a covariate law `F*` and a baseline `α*`. The model gives treatment `t`
the surface `m_t = g⁻¹ ∘ η_t` at baseline `α*`, and the two target estimands of `b` against `a`
on the link scale `g` are the library's

* **marginal effect** `linkMarginal g F* m_a m_b = g(∫ m_b dF*) - g(∫ m_a dF*)`, the link
  applied to the target arm means `MultilevelModel.armMean`, and
* **average conditional effect** `linkConditional g F* m_a m_b = ∫ (g(m_b) - g(m_a)) dF*`.

## Main results

* **The conditional estimand needs only the covariate mean** (`linkConditional_surface`): it is
  `(γ_b - γ_a) + x̄*ᵀ(β₂,b - β₂,a)`, free of the baseline and of `β₁`. Under the shared effect
  modifier assumption for `{a, b}` it is `γ_b - γ_a` in every target
  (`linkConditional_surface_of_shared`).
* **On a directly collapsible scale the two estimands agree**
  (`linkMarginal_surface_of_collapsible`), in particular on the identity link
  (`linkMarginal_surface_id`).
* **Identification in the target** (`integral_condContrast_eq_linkConditional`,
  `pointIdentified_target_marginalEffect`, `pointIdentified_target_condContrast`): if the model
  surfaces are the conditional means of the potential outcomes in the target population, the
  causal marginal effect `g(E*[Y(b)]) - g(E*[Y(a)])` and the population average of the
  conditional effect `E*[g(E*[Y(b) | X]) - g(E*[Y(a) | X])]` are functions of the coefficients,
  the target baseline and the target covariate law alone: they are the two estimands above.
  The arm level step is `Population.marginalEffect_eq_linkMarginal`.

## References

* D. M. Phillippo, S. Dias, A. E. Ades, M. Belger, A. Brnabic, A. Schacht, D. Saure, Z. Kadziola
  and N. J. Welton, *Multilevel network meta-regression for population-adjusted treatment
  comparisons*, Journal of the Royal Statistical Society Series A 183 (2020).
-/

@[expose] public section

namespace CausalInference

namespace NetworkMetaRegression

open MeasureTheory ProbabilityTheory EffectMeasure IndirectComparison NetworkMetaAnalysis

namespace MultilevelModel

variable {J K : Type*} {p : ℕ}

/-! ### The conditional and the marginal estimand -/

/-- **The conditional estimand in a target population.** If `g (g⁻¹ y) = y` for every `y` and the
target covariate law `F*` is a probability law with integrable coordinates, the average
conditional effect of `b` against `a` at any baseline is `(γ_b - γ_a) + x̄*ᵀ(β₂,b - β₂,a)`. -/
theorem linkConditional_surface {g ginv : ℝ → ℝ} (hg : ∀ y, g (ginv y) = y)
    (M : MultilevelModel J K p) (α : ℝ) {F : Measure (Fin p → ℝ)} [IsProbabilityMeasure F]
    (hF : ∀ i, Integrable (fun x : Fin p → ℝ => x i) F) (a b : K) :
    linkConditional g F (M.surface ginv α a) (M.surface ginv α b) =
      (M.γ b - M.γ a) + covMean F ⬝ᵥ (M.β₂ b - M.β₂ a) := by
  have e : ∀ k, M.surface ginv α k = fun x => ginv ((M.atBaseline α).predictor k x) :=
    fun k => funext fun x => by rw [surface, eta_eq_predictor]
  rw [e, e, AnchoredModel.linkConditional_predictor hg _ hF]
  rfl

/-- **Under shared effect modifiers the conditional estimand is the same in every target**:
`γ_b - γ_a`, whatever the covariate law and the baseline. -/
theorem linkConditional_surface_of_shared {g ginv : ℝ → ℝ} (hg : ∀ y, g (ginv y) = y)
    {M : MultilevelModel J K p} {a b : K} (hS : M.SharedEffectModifiers {a, b}) (α : ℝ)
    {F : Measure (Fin p → ℝ)} [IsProbabilityMeasure F]
    (hF : ∀ i, Integrable (fun x : Fin p → ℝ => x i) F) :
    linkConditional g F (M.surface ginv α a) (M.surface ginv α b) = M.γ b - M.γ a := by
  have h : M.β₂ b = M.β₂ a := hS b (by simp) a (by simp)
  rw [linkConditional_surface hg M α hF, h, sub_self, dotProduct_zero, add_zero]

/-- **On a directly collapsible scale the marginal estimand is the conditional one.** If the
scale `g` with mean space `D` is directly collapsible, `g (g⁻¹ y) = y`, the two target surfaces
are integrable with values almost surely in `D`, and `F*` has integrable coordinates, then the
marginal estimand equals the conditional estimand, `(γ_b - γ_a) + x̄*ᵀ(β₂,b - β₂,a)`. -/
theorem linkMarginal_surface_of_collapsible {D : Set ℝ} {g ginv : ℝ → ℝ}
    (hcoll : LinkDirectlyCollapsible D g) (hg : ∀ y, g (ginv y) = y) (M : MultilevelModel J K p)
    (α : ℝ) {F : Measure (Fin p → ℝ)} [IsProbabilityMeasure F]
    (hF : ∀ i, Integrable (fun x : Fin p → ℝ => x i) F) (a b : K)
    (ha : Integrable (M.surface ginv α a) F) (hb : Integrable (M.surface ginv α b) F)
    (hD : ∀ᵐ x ∂F, M.surface ginv α a x ∈ D ∧ M.surface ginv α b x ∈ D) :
    linkMarginal g F (M.surface ginv α a) (M.surface ginv α b) =
        linkConditional g F (M.surface ginv α a) (M.surface ginv α b) ∧
      linkMarginal g F (M.surface ginv α a) (M.surface ginv α b) =
        (M.γ b - M.γ a) + covMean F ⬝ᵥ (M.β₂ b - M.β₂ a) := by
  have hi : Integrable (linkContrast g (M.surface ginv α a) (M.surface ginv α b)) F := by
    have e : linkContrast g (M.surface ginv α a) (M.surface ginv α b) =
        fun x => (M.γ b - M.γ a) + ∑ i, x i * (M.β₂ b - M.β₂ a) i :=
      funext fun x => linkContrast_surface hg M α a b x
    rw [e]
    exact (integrable_const _).add (integrable_finsetSum _ fun i _ => (hF i).mul_const _)
  have h := hcoll (Fin p → ℝ) F _ _ ha hb hD hi
  exact ⟨h, h.trans (linkConditional_surface hg M α hF a b)⟩

/-- **On the identity link the marginal and the conditional estimand agree**, for every covariate
law with integrable coordinates: both are `(γ_b - γ_a) + x̄*ᵀ(β₂,b - β₂,a)`. -/
theorem linkMarginal_surface_id (M : MultilevelModel J K p) (α : ℝ) {F : Measure (Fin p → ℝ)}
    [IsProbabilityMeasure F] (hF : ∀ i, Integrable (fun x : Fin p → ℝ => x i) F) (a b : K) :
    linkMarginal id F (M.surface id α a) (M.surface id α b) =
        linkConditional id F (M.surface id α a) (M.surface id α b) ∧
      linkMarginal id F (M.surface id α a) (M.surface id α b) =
        (M.γ b - M.γ a) + covMean F ⬝ᵥ (M.β₂ b - M.β₂ a) :=
  linkMarginal_surface_of_collapsible linkDirectlyCollapsible_id (fun _ => rfl) M α hF a b
    (M.integrable_eta hF α a) (M.integrable_eta hF α b) (ae_of_all _ fun _ => ⟨trivial, trivial⟩)

end MultilevelModel

/-! ### Identification in the target population -/

section Target

variable {Ω : Type*} [MeasurableSpace Ω] {K : Type*} {p : ℕ}

/-- **The population average of the conditional effect is the conditional estimand of the
covariate law.** In a population whose covariates `X` are measurable, if `m_a` and `m_b` are
conditional mean functions of `Y(a)` and `Y(b)` and the link `g` is measurable, then
`E[g(E[Y(b) | X]) - g(E[Y(a) | X])] = linkConditional g P_X m_a m_b`. -/
theorem integral_condContrast_eq_linkConditional {𝒳 : Type*} [MeasurableSpace 𝒳]
    {P : Population Ω 𝒳 K} (hX : Measurable P.X) {g : ℝ → ℝ} (hgm : Measurable g) {a b : K}
    {ma mb : 𝒳 → ℝ} (ha : P.IsCondMean a ma) (hb : P.IsCondMean b mb) :
    ∫ ω, (g (P.μ[P.Y b | MeasurableSpace.comap P.X inferInstance] ω) -
        g (P.μ[P.Y a | MeasurableSpace.comap P.X inferInstance] ω)) ∂P.μ =
      linkConditional g P.covLaw ma mb := by
  have h1 : (fun ω => g (P.μ[P.Y b | MeasurableSpace.comap P.X inferInstance] ω) -
      g (P.μ[P.Y a | MeasurableSpace.comap P.X inferInstance] ω)) =ᵐ[P.μ]
      fun ω => linkContrast g ma mb (P.X ω) := by
    filter_upwards [ha.2, hb.2] with ω hωa hωb
    simp only [linkContrast, ← hωa, ← hωb]
  rw [integral_congr_ae h1, linkConditional, Population.covLaw,
    integral_map hX.aemeasurable (f := linkContrast g ma mb)
      ((hgm.comp hb.1).sub (hgm.comp ha.1)).aestronglyMeasurable]

/-- The class of **target populations correctly described by the model**: the population law is
a probability law, the covariates are measurable, every potential outcome is integrable, and the
model surface of every treatment at the target baseline is its conditional mean function. A
member is a population `P`, model coefficients `M` (study intercepts included but unused) and a
target baseline `α`. -/
def TargetClass (J : Type*) (ginv : ℝ → ℝ) :
    Set (Population Ω (Fin p → ℝ) K × MultilevelModel J K p × ℝ) :=
  {m | IsProbabilityMeasure m.1.μ ∧ Measurable m.1.X ∧
    ∀ t, Integrable (m.1.Y t) m.1.μ ∧ m.1.IsCondMean t (m.2.1.surface ginv m.2.2 t)}

/-- **The target marginal effect is identified from the model and the target covariate law.**
On `TargetClass`, the causal marginal effect `g(E*[Y(b)]) - g(E*[Y(a)])` equals the marginal
estimand `linkMarginal g F* m_a m_b` of the target covariate law `F*` and the model surfaces at
the target baseline; so it is point identified from the coefficients, the baseline and `F*`. -/
theorem marginalEffect_eq_target {J : Type*} {ginv : ℝ → ℝ}
    {m : Population Ω (Fin p → ℝ) K × MultilevelModel J K p × ℝ}
    (hm : m ∈ TargetClass (Ω := Ω) (p := p) J ginv) (g : ℝ → ℝ) (a b : K) :
    m.1.marginalEffect g a b =
      linkMarginal g m.1.covLaw (m.2.1.surface ginv m.2.2 a) (m.2.1.surface ginv m.2.2 b) := by
  have := hm.1
  exact Population.marginalEffect_eq_linkMarginal g hm.2.1 (hm.2.2 a).1 (hm.2.2 b).1
    (hm.2.2 a).2 (hm.2.2 b).2

/-- **Identification of the target marginal effect**: on `TargetClass` the causal marginal effect
is a function of the coefficients `(β₁, γ, β₂)`, the target baseline and the target covariate law
(`marginalEffect_eq_target`). -/
theorem pointIdentified_target_marginalEffect {J : Type*} (ginv g : ℝ → ℝ) (a b : K) :
    PointIdentified (TargetClass (Ω := Ω) (p := p) J ginv)
      (fun m => (m.2.1.β₁, m.2.1.γ, m.2.1.β₂, m.2.2, m.1.covLaw))
      (fun m => m.1.marginalEffect g a b) := by
  intro m hm m' hm' ho
  simp only [Prod.mk.injEq] at ho
  obtain ⟨h1, h2, h3, h4, h5⟩ := ho
  simp only
  rw [marginalEffect_eq_target hm, marginalEffect_eq_target hm', h5]
  have e : ∀ t, m.2.1.surface ginv m.2.2 t = m'.2.1.surface ginv m'.2.2 t := fun t =>
    funext fun x => by
      simp only [MultilevelModel.surface, MultilevelModel.eta, h1, h2, h3, h4]
  rw [e, e]

/-- **The target average conditional effect is identified.** On `TargetClass`, if the link `g`
is measurable, the population average `E*[g(E*[Y(b) | X]) - g(E*[Y(a) | X])]` of the conditional
effect is the conditional estimand `linkConditional g F* m_a m_b`, so it is point identified from
the coefficients, the target baseline and the target covariate law. -/
theorem pointIdentified_target_condContrast {J : Type*} (ginv : ℝ → ℝ) {g : ℝ → ℝ}
    (hgm : Measurable g) (a b : K) :
    PointIdentified (TargetClass (Ω := Ω) (p := p) J ginv)
      (fun m => (m.2.1.β₁, m.2.1.γ, m.2.1.β₂, m.2.2, m.1.covLaw))
      (fun m => ∫ ω, (g (m.1.μ[m.1.Y b | MeasurableSpace.comap m.1.X inferInstance] ω) -
        g (m.1.μ[m.1.Y a | MeasurableSpace.comap m.1.X inferInstance] ω)) ∂m.1.μ) := by
  intro m hm m' hm' ho
  simp only [Prod.mk.injEq] at ho
  obtain ⟨h1, h2, h3, h4, h5⟩ := ho
  simp only
  rw [integral_condContrast_eq_linkConditional hm.2.1 hgm (hm.2.2 a).2 (hm.2.2 b).2,
    integral_condContrast_eq_linkConditional hm'.2.1 hgm (hm'.2.2 a).2 (hm'.2.2 b).2, h5]
  have e : ∀ t, m.2.1.surface ginv m.2.2 t = m'.2.1.surface ginv m'.2.2 t := fun t =>
    funext fun x => by
      simp only [MultilevelModel.surface, MultilevelModel.eta, h1, h2, h3, h4]
  rw [e, e]

end Target

end NetworkMetaRegression

end CausalInference
