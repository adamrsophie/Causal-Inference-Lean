/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.NetworkMetaRegression.SharedModifiersManifold
public import CausalInference.NetworkMetaRegression.Examples
public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv

/-!
# A nonzero sensitivity breaks identification of the target effect

In the two study network without shared effect modifiers (individual data on `a` and `c`,
aggregate data on `b` and `c`), the parameters `w = (β₂,b, γ_b)` of `b` enter the observable data
only through the aggregate mean `Θ(w)` of arm `b` in the aggregate study (baseline `α_bc`,
covariate law `F_bc`); every other surface is free of `w` (`MultilevelModel.surface_withArm_of_ne`).
Along a level curve `β ↦ (β, φ(β))` of `Θ` (`coefMean_implicit`) the data are constant.

**What "necessary" means here.** The results below are non identification results in this data
configuration: if the target effect of `b` against `a` moves along the level curve at one point,
then there are two parameter values on that curve with the same observable data and different
target effects, so the effect is not point identified (`PointIdentified`), also over the target
populations of `TargetClass`. They do not say that shared effect modifiers are
needed in every network: with individual data on `b` the network theorems identify `β₂,b`
(`network_identifiable_of_class`).

## Main definitions

* `sensitivity Dbc Ds`: the derivative `v ↦ Ds(v, ∇φ v)` of the target mean of `b` along the
  level curve, where `∇φ = implicitGrad Dbc`; in coordinates
  `S_i = E*[g⁻¹'(η*) X_i] - E*[g⁻¹'(η*)] E_bc[g⁻¹'(η) X_i] / E_bc[g⁻¹'(η)]`
  (`sensitivity_apply_single`).
* `tiltedMean F g⁻¹' α β₁ w`: the mean of the covariates reweighted by `g⁻¹'(η_w)`,
  `E[g⁻¹'(η) X] / E[g⁻¹'(η)]`.
* `surfacePopulation F N g⁻¹ α`: the population on the covariate space with law `F` whose
  potential outcomes are the surfaces of `N` at baseline `α`; it belongs to `TargetClass`.

## Main results

* `hasFDerivAt_targetMarginal_along`: along the level curve the target marginal effect
  `g(E*[m_b]) - g(E*[m_a])` has the derivative `S / g⁻¹'(g(E*[m_b]))`, by the inverse function
  theorem for the link.
* `not_pointIdentified_of_hasFDerivAt`, `not_pointIdentified_withArm_marginal`,
  `not_pointIdentified_targetClass_marginal`: if `S ≠ 0` at one parameter value, the target
  marginal effect is not point identified.
* `sensitivity_ne_zero_iff`: `S ≠ 0` exactly when the tilted covariate means of the target and of
  the aggregate study differ.
* `withArm_conditional_not_identified`: the conditional effect at a covariate value `x₀` moves
  along the curve with derivative `v ↦ (x₀ - tiltedMean)ᵀ v`, so it is not identified when `x₀`
  differs from the tilted mean of the aggregate study.
* Identity link (`identity_marginal_not_identified`, `identity_conditional_not_identified`):
  `S = x̄* - x̄_bc`, so the target effect is not identified when the target covariate mean differs
  from the aggregate study covariate mean; the conditional effect at `x₀` when `x₀ ≠ x̄_bc`.
* Instances: `logit_solution_graph_instance`, `identity_not_identified_instance`.
-/

@[expose] public section

namespace CausalInference

namespace NetworkMetaRegression

open MeasureTheory ProbabilityTheory Filter Topology Set EffectMeasure IndirectComparison

variable {p : ℕ}

/-! ### The sensitivity vector -/

/-- The **sensitivity** of the target mean along the level curve of the aggregate mean: with `Dbc`
the derivative of the aggregate mean and `Ds` that of the target mean, `v ↦ Ds(v, ∇φ v)` with
`∇φ = implicitGrad Dbc`. -/
noncomputable def sensitivity (Dbc Ds : (Fin p → ℝ) × ℝ →L[ℝ] ℝ) : (Fin p → ℝ) →L[ℝ] ℝ :=
  Ds.comp ((ContinuousLinearMap.id ℝ (Fin p → ℝ)).prod (implicitGrad Dbc))

/-- For `Dbc(0, 1) ≠ 0`, `S(v) = Ds(v, 0) - Ds(0, 1) Dbc(v, 0) / Dbc(0, 1)`. -/
theorem sensitivity_apply (Dbc Ds : (Fin p → ℝ) × ℝ →L[ℝ] ℝ) (hD : Dbc (0, 1) ≠ 0)
    (v : Fin p → ℝ) :
    sensitivity Dbc Ds v = Ds (v, 0) - Ds (0, 1) * Dbc (v, 0) / Dbc (0, 1) := by
  simp only [sensitivity, ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply,
    ContinuousLinearMap.id_apply]
  rw [clm_prod_apply_eq_add, implicitGrad_apply _ hD]
  ring

/-- The **tilted covariate mean** `E[g⁻¹'(η_w) X] / E[g⁻¹'(η_w)]`. -/
noncomputable def tiltedMean (F : Measure (Fin p → ℝ)) (ginv' : ℝ → ℝ) (α : ℝ) (β₁ : Fin p → ℝ)
    (w : (Fin p → ℝ) × ℝ) : Fin p → ℝ := fun i =>
  (∫ x, ginv' (coefPred α β₁ x w) * x i ∂F) / ∫ x, ginv' (coefPred α β₁ x w) ∂F

/-- A linear functional on `ℝ^p` vanishes exactly when it vanishes on the standard basis. -/
theorem clm_eq_zero_iff_single (L : (Fin p → ℝ) →L[ℝ] ℝ) :
    L = 0 ↔ ∀ i, L (Pi.single i 1) = 0 := by
  refine ⟨fun h i => by simp [h], fun h => ?_⟩
  refine ContinuousLinearMap.coe_injective (LinearMap.pi_ext fun i x => ?_)
  have : (Pi.single i x : Fin p → ℝ) = x • Pi.single i (1 : ℝ) := by
    ext j; by_cases hj : j = i <;> simp [hj]
  simp [this, h i]

section Coordinates

variable {Fbc Fs : Measure (Fin p → ℝ)} [IsProbabilityMeasure Fbc] [IsProbabilityMeasure Fs]
  {ginv' : ℝ → ℝ} {C : ℝ} (hd' : Continuous ginv') (hpos : ∀ t, 0 < ginv' t)
  (hbd : ∀ t, |ginv' t| ≤ C) (hFbc : ∀ i, Integrable (fun x : Fin p → ℝ => x i) Fbc)
  (hFs : ∀ i, Integrable (fun x : Fin p → ℝ => x i) Fs) {αbc αs : ℝ} {β₁ : Fin p → ℝ}
include hd' hbd hFbc hFs

include hpos in
/-- **The sensitivity in coordinates**:
`S_i = E*[g⁻¹'(η*) X_i] - E*[g⁻¹'(η*)] E_bc[g⁻¹'(η) X_i] / E_bc[g⁻¹'(η)]`. -/
theorem sensitivity_apply_single (w : (Fin p → ℝ) × ℝ) (i : Fin p) :
    sensitivity (coefMeanDeriv Fbc ginv' αbc β₁ w) (coefMeanDeriv Fs ginv' αs β₁ w)
        (Pi.single i 1) =
      (∫ x, ginv' (coefPred αs β₁ x w) * x i ∂Fs) -
        (∫ x, ginv' (coefPred αs β₁ x w) ∂Fs) * (∫ x, ginv' (coefPred αbc β₁ x w) * x i ∂Fbc) /
          ∫ x, ginv' (coefPred αbc β₁ x w) ∂Fbc := by
  rw [sensitivity_apply _ _ (coefMeanDeriv_snd_pos hd' hbd hFbc hpos w).ne',
    coefMeanDeriv_fst hd' hbd hFs, coefMeanDeriv_snd hd' hbd hFs,
    coefMeanDeriv_fst hd' hbd hFbc, coefMeanDeriv_snd hd' hbd hFbc]

include hpos in
/-- **The sensitivity vanishes exactly when the tilted means agree**: `S_i` is
`E*[g⁻¹'(η*)]` times the difference of the `i`-th tilted means of the target and of the
aggregate study. -/
theorem sensitivity_ne_zero_iff (w : (Fin p → ℝ) × ℝ) :
    sensitivity (coefMeanDeriv Fbc ginv' αbc β₁ w) (coefMeanDeriv Fs ginv' αs β₁ w) ≠ 0 ↔
      tiltedMean Fs ginv' αs β₁ w ≠ tiltedMean Fbc ginv' αbc β₁ w := by
  have hs : 0 < ∫ x, ginv' (coefPred αs β₁ x w) ∂Fs := by
    rw [← coefMeanDeriv_snd hd' hbd hFs]; exact coefMeanDeriv_snd_pos hd' hbd hFs hpos w
  have hb : 0 < ∫ x, ginv' (coefPred αbc β₁ x w) ∂Fbc := by
    rw [← coefMeanDeriv_snd hd' hbd hFbc]; exact coefMeanDeriv_snd_pos hd' hbd hFbc hpos w
  have key : ∀ i, sensitivity (coefMeanDeriv Fbc ginv' αbc β₁ w)
      (coefMeanDeriv Fs ginv' αs β₁ w) (Pi.single i 1) =
      (∫ x, ginv' (coefPred αs β₁ x w) ∂Fs) *
        (tiltedMean Fs ginv' αs β₁ w i - tiltedMean Fbc ginv' αbc β₁ w i) := fun i => by
    rw [sensitivity_apply_single hd' hpos hbd hFbc hFs, tiltedMean, tiltedMean]
    field_simp
  rw [Ne, clm_eq_zero_iff_single, Ne, funext_iff]
  simp only [key, mul_eq_zero, hs.ne', false_or, sub_eq_zero]

end Coordinates

/-- The sensitivity of the linear predictor at a covariate value `x₀`:
`S_i = x₀_i - E_bc[g⁻¹'(η) X_i] / E_bc[g⁻¹'(η)]`. -/
theorem sensitivity_coefDir_apply_single {F : Measure (Fin p → ℝ)} [IsProbabilityMeasure F]
    {ginv' : ℝ → ℝ} {C : ℝ} (hd' : Continuous ginv') (hpos : ∀ t, 0 < ginv' t)
    (hbd : ∀ t, |ginv' t| ≤ C) (hF : ∀ i, Integrable (fun x : Fin p → ℝ => x i) F) {α : ℝ}
    {β₁ : Fin p → ℝ} (w : (Fin p → ℝ) × ℝ) (x₀ : Fin p → ℝ) (i : Fin p) :
    sensitivity (coefMeanDeriv F ginv' α β₁ w) (coefDir x₀) (Pi.single i 1) =
      x₀ i - tiltedMean F ginv' α β₁ w i := by
  rw [sensitivity_apply _ _ (coefMeanDeriv_snd_pos hd' hbd hF hpos w).ne', coefDir_apply,
    coefDir_apply, coefMeanDeriv_fst hd' hbd hF,
    coefMeanDeriv_snd hd' hbd hF, tiltedMean]
  simp [dotProduct_single]

/-- The sensitivity of the linear predictor at `x₀` vanishes exactly when `x₀` is the tilted
covariate mean of the aggregate study. -/
theorem sensitivity_coefDir_ne_zero_iff {F : Measure (Fin p → ℝ)} [IsProbabilityMeasure F]
    {ginv' : ℝ → ℝ} {C : ℝ} (hd' : Continuous ginv') (hpos : ∀ t, 0 < ginv' t)
    (hbd : ∀ t, |ginv' t| ≤ C) (hF : ∀ i, Integrable (fun x : Fin p → ℝ => x i) F) {α : ℝ}
    {β₁ : Fin p → ℝ} (w : (Fin p → ℝ) × ℝ) (x₀ : Fin p → ℝ) :
    sensitivity (coefMeanDeriv F ginv' α β₁ w) (coefDir x₀) ≠ 0 ↔
      x₀ ≠ tiltedMean F ginv' α β₁ w := by
  rw [Ne, clm_eq_zero_iff_single, Ne, funext_iff]
  simp only [sensitivity_coefDir_apply_single hd' hpos hbd hF, sub_eq_zero]

/-- Under the identity link (`g⁻¹' = 1`) the tilted mean is the covariate mean. -/
theorem tiltedMean_one (F : Measure (Fin p → ℝ)) [IsProbabilityMeasure F] (α : ℝ)
    (β₁ : Fin p → ℝ) (w : (Fin p → ℝ) × ℝ) : tiltedMean F (fun _ => 1) α β₁ w = covMean F := by
  funext i
  simp [tiltedMean, covMean]

/-! ### Non identification from a nonzero derivative -/

/-- **A nonzero derivative along a data preserving curve breaks point identification.** If a
curve `c` of parameter values in `S` keeps the observable data constant near `β₀` and the target
`θ ∘ c` has a nonzero derivative at `β₀`, then `θ` is not point identified on `S`. -/
theorem not_pointIdentified_of_hasFDerivAt {M O : Type*} {S : Set M} {obs : M → O}
    {θ : M → ℝ} {c : (Fin p → ℝ) → M} {β₀ : Fin p → ℝ} {L : (Fin p → ℝ) →L[ℝ] ℝ}
    (hS : ∀ β, c β ∈ S) (hobs : ∀ᶠ β in 𝓝 β₀, obs (c β) = obs (c β₀))
    (hθ : HasFDerivAt (fun β => θ (c β)) L β₀) (hL : L ≠ 0) : ¬PointIdentified S obs θ := by
  intro h
  apply hL
  refine hθ.unique ((hasFDerivAt_const (θ (c β₀)) β₀).congr_of_eventuallyEq ?_)
  filter_upwards [hobs] with β hβ
  exact h _ (hS β) _ (hS β₀) hβ

namespace MultilevelModel

variable {J K : Type*} [DecidableEq K]

/-- The observable data of the two study network: the surfaces of `a` and `c` at the baseline of
the individual data study `jac`, and the aggregate means of `b` and `c` under the covariate law
`F_bc` at the baseline of the aggregate study `jbc`. -/
noncomputable def twoStudyData (ginv : ℝ → ℝ) (Fbc : Measure (Fin p → ℝ)) (jac jbc : J)
    (a b c : K) (N : MultilevelModel J K p) :
    ((Fin p → ℝ) → ℝ) × ((Fin p → ℝ) → ℝ) × ℝ × ℝ :=
  (N.surface ginv (N.μ jac) a, N.surface ginv (N.μ jac) c, N.armMean ginv (N.μ jbc) Fbc b,
    N.armMean ginv (N.μ jbc) Fbc c)

/-- Replacing the parameters of `b` keeps the data when it keeps the aggregate mean of `b`. -/
theorem twoStudyData_withArm (ginv : ℝ → ℝ) (Fbc : Measure (Fin p → ℝ)) {jac jbc : J}
    {a b c : K} (hab : a ≠ b) (hcb : c ≠ b) (M : MultilevelModel J K p) (w : (Fin p → ℝ) × ℝ)
    (h : (M.withArm b w).armMean ginv (M.μ jbc) Fbc b = M.armMean ginv (M.μ jbc) Fbc b) :
    twoStudyData ginv Fbc jac jbc a b c (M.withArm b w) =
      twoStudyData ginv Fbc jac jbc a b c M := by
  have hc' : (M.withArm b w).armMean ginv (M.μ jbc) Fbc c = M.armMean ginv (M.μ jbc) Fbc c := by
    simp only [armMean, surface_withArm_of_ne ginv M hcb]
  rw [twoStudyData, twoStudyData, withArm_μ, surface_withArm_of_ne ginv M hab,
    surface_withArm_of_ne ginv M hcb, h, hc']

omit [DecidableEq K] in
theorem armMean_eq_coefMean (ginv : ℝ → ℝ) (M : MultilevelModel J K p) (α : ℝ)
    (F : Measure (Fin p → ℝ)) (k : K) :
    M.armMean ginv α F k = coefMean F ginv α M.β₁ (M.β₂ k, M.γ k) := by
  simp only [armMean, surface, coefMean, coefPred, eta_eq_affine]

/-- The population on the covariate space with law `F`, covariates the identity, and potential
outcomes the surfaces of `N` at baseline `α`. -/
noncomputable def surfacePopulation (F : Measure (Fin p → ℝ)) (N : MultilevelModel J K p)
    (ginv : ℝ → ℝ) (α : ℝ) : Population (Fin p → ℝ) (Fin p → ℝ) K :=
  ⟨F, id, fun t => N.surface ginv α t⟩

section Curve

variable {Fbc Fs : Measure (Fin p → ℝ)} [IsProbabilityMeasure Fbc] [IsProbabilityMeasure Fs]
  {ginv ginv' : ℝ → ℝ} {C : ℝ} (hd : ∀ t, HasDerivAt ginv (ginv' t) t) (hd' : Continuous ginv')
  (hpos : ∀ t, 0 < ginv' t) (hbd : ∀ t, |ginv' t| ≤ C)
  (hFbc : ∀ i, Integrable (fun x : Fin p → ℝ => x i) Fbc)
  (hFs : ∀ i, Integrable (fun x : Fin p → ℝ => x i) Fs)

omit [DecidableEq K] in
include hd hbd hFs in
/-- Every surface population of a model is a member of `TargetClass`. -/
theorem surfacePopulation_mem_targetClass (N : MultilevelModel J K p) (α : ℝ) :
    (surfacePopulation Fs N ginv α, N, α) ∈ TargetClass (Ω := Fin p → ℝ) J ginv := by
  have hcont : Continuous ginv := continuous_iff_continuousAt.2 fun t => (hd t).continuousAt
  have he : ∀ t, N.surface ginv α t = fun x => ginv ((α + N.γ t) + x ⬝ᵥ (N.β₁ + N.β₂ t)) :=
    fun t => funext fun x => by simp only [surface, eta_eq_affine]
  have hsc : ∀ t, Continuous (N.surface ginv α t) := fun t => by
    rw [he]; exact hcont.comp (by unfold dotProduct; fun_prop)
  have hint : ∀ t, Integrable (N.surface ginv α t) Fs := fun t => by
    rw [he]; exact integrable_inv_link_affine hd hbd hFs _ _
  refine ⟨‹_›, measurable_id, fun t => ⟨hint t, (hsc t).measurable, ?_⟩⟩
  change (fun ω => N.surface ginv α t (id ω)) =ᵐ[Fs]
    Fs[N.surface ginv α t | MeasurableSpace.comap id inferInstance]
  have hsm : StronglyMeasurable[MeasurableSpace.comap id inferInstance] (N.surface ginv α t) := by
    rw [MeasurableSpace.comap_id]; exact (hsc t).measurable.stronglyMeasurable
  rw [condExp_of_stronglyMeasurable measurable_id.comap_le hsm (hint t)]
  rfl

include hd hd' hpos hbd hFbc in
/-- **The level curve through `M`.** There is a function `φ` with `φ(β₂,b) = γ_b` such that the
models `M.withArm b (β, φ β)` keep the aggregate mean of `b` in the aggregate study for `β` near
`β₂,b`, with gradient the implicit gradient. -/
theorem exists_withArm_level_curve (M : MultilevelModel J K p) (b : K) (jbc : J) :
    ∃ φ : (Fin p → ℝ) → ℝ, φ (M.β₂ b) = M.γ b ∧
      (∀ᶠ β in 𝓝 (M.β₂ b), (M.withArm b (β, φ β)).armMean ginv (M.μ jbc) Fbc b =
        M.armMean ginv (M.μ jbc) Fbc b) ∧
      HasFDerivAt φ (implicitGrad (coefMeanDeriv Fbc ginv' (M.μ jbc) M.β₁ (M.β₂ b, M.γ b)))
        (M.β₂ b) := by
  obtain ⟨φ, h0, hev, hder⟩ :=
    coefMean_implicit hd hd' hpos hbd hFbc (α := M.μ jbc) (β₁ := M.β₁) (M.β₂ b) (M.γ b)
  refine ⟨φ, h0, ?_, hder⟩
  filter_upwards [hev] with β hβ
  rw [armMean_withArm, armMean_eq_coefMean, hβ]

include hd hd' hpos hbd hFs in
/-- **The closed form derivative of the target marginal effect along the curve.** For a link `g`
inverting `g⁻¹`, along a curve `β ↦ M.withArm b (β, φ β)` through `M` with gradient
`implicitGrad Dbc`, the target marginal effect `g(E*[m_b]) - g(E*[m_a])` has derivative
`S / g⁻¹'(g(E*[m_b]))`, with `S = sensitivity Dbc DΘ*` and `DΘ*` the derivative of the target
mean of `b`. -/
theorem hasFDerivAt_targetMarginal_along {g : ℝ → ℝ} (hg : ∀ t, g (ginv t) = t)
    (M : MultilevelModel J K p) {a b : K} (hab : a ≠ b) (αs : ℝ) {φ : (Fin p → ℝ) → ℝ}
    {Dbc : (Fin p → ℝ) × ℝ →L[ℝ] ℝ} (hφ0 : φ (M.β₂ b) = M.γ b)
    (hφ : HasFDerivAt φ (implicitGrad Dbc) (M.β₂ b)) :
    HasFDerivAt (fun β => linkMarginal g Fs ((M.withArm b (β, φ β)).surface ginv αs a)
        ((M.withArm b (β, φ β)).surface ginv αs b))
      ((ginv' (g (M.armMean ginv αs Fs b)))⁻¹ •
        sensitivity Dbc (coefMeanDeriv Fs ginv' αs M.β₁ (M.β₂ b, M.γ b))) (M.β₂ b) := by
  have hcont : Continuous ginv := continuous_iff_continuousAt.2 fun t => (hd t).continuousAt
  have hmono : StrictMono ginv := strictMono_of_hasDerivAt_pos hd hpos
  have e : (fun β => linkMarginal g Fs ((M.withArm b (β, φ β)).surface ginv αs a)
      ((M.withArm b (β, φ β)).surface ginv αs b)) =
      fun β => g (coefMean Fs ginv αs M.β₁ (β, φ β)) - g (∫ x, M.surface ginv αs a x ∂Fs) := by
    funext β
    rw [linkMarginal, surface_withArm_of_ne ginv M hab, ← armMean_withArm ginv M b (β, φ β) αs Fs]
    rfl
  have h1 := hasFDerivAt_coefMean hd hd' hbd hFs (α := αs) (β₁ := M.β₁) (M.β₂ b, φ (M.β₂ b))
  have h2 := h1.comp (M.β₂ b) ((hasFDerivAt_id (M.β₂ b)).prodMk hφ)
  rw [hφ0] at h2
  set y₀ := M.armMean ginv αs Fs b with hy₀
  have hy : y₀ ∈ Set.range ginv := by
    have hdot : Measurable fun x : Fin p → ℝ => x ⬝ᵥ (M.β₁ + M.β₂ b) :=
      (by unfold dotProduct; fun_prop : Continuous fun x : Fin p → ℝ =>
        x ⬝ᵥ (M.β₁ + M.β₂ b)).measurable
    rw [← range_shiftMean (F := Fs) hmono hcont hdot
      (fun c => integrable_inv_link_affine hd hbd hFs c _)]
    exact ⟨αs + M.γ b, by rw [hy₀, armMean_eq_coefMean, coefMean_eq_shiftMean]⟩
  obtain ⟨t₀, ht₀⟩ := hy
  have hgt : g y₀ = t₀ := by rw [← ht₀, hg]
  have hstrict : HasStrictDerivAt ginv (ginv' t₀) t₀ :=
    hasStrictDerivAt_of_hasDerivAt_of_continuousAt (Eventually.of_forall hd) hd'.continuousAt
  have hgd := (hstrict.to_local_left_inverse (hpos t₀).ne' (Eventually.of_forall hg)).hasDerivAt
  rw [ht₀, ← hgt] at hgd
  have h3 := hgd.comp_hasFDerivAt_of_eq (M.β₂ b) h2
    (by simp only [Function.comp, hy₀, armMean_eq_coefMean, id, hφ0])
  rw [e]
  exact (hasFDerivAt_sub_const_iff _).2 h3

include hd hd' hpos hbd hFbc hFs in
/-- **Non identification of the target marginal effect.** In the two study network (individual
data on `a` and `c` in study `jac`, aggregate data on `b` and `c` in study `jbc` with covariate
law `F_bc`), let `g` invert `g⁻¹`. If the sensitivity `S` of the target mean of `b` (target law
`F*`, baseline `α*`) along the level curve is nonzero at `M`, then the target marginal effect
`g(E*[m_b]) - g(E*[m_a])` is not point identified from the data, even among the models that
differ from `M` only in `(β₂,b, γ_b)`. -/
theorem not_pointIdentified_withArm_marginal {g : ℝ → ℝ} (hg : ∀ t, g (ginv t) = t)
    (M : MultilevelModel J K p) {jac jbc : J} {a b c : K} (hab : a ≠ b) (hcb : c ≠ b) (αs : ℝ)
    (hS : sensitivity (coefMeanDeriv Fbc ginv' (M.μ jbc) M.β₁ (M.β₂ b, M.γ b))
      (coefMeanDeriv Fs ginv' αs M.β₁ (M.β₂ b, M.γ b)) ≠ 0) :
    ¬PointIdentified (Set.range (M.withArm b)) (twoStudyData ginv Fbc jac jbc a b c)
      (fun N => linkMarginal g Fs (N.surface ginv αs a) (N.surface ginv αs b)) := by
  obtain ⟨φ, h0, hev, hφ⟩ := exists_withArm_level_curve hd hd' hpos hbd hFbc M b jbc
  refine not_pointIdentified_of_hasFDerivAt (c := fun β => M.withArm b (β, φ β))
    (fun β => ⟨_, rfl⟩) ?_ (hasFDerivAt_targetMarginal_along hd hd' hpos hbd hFs hg M hab αs h0 hφ)
    (smul_ne_zero (inv_ne_zero (hpos _).ne') hS)
  filter_upwards [hev] with β hβ
  rw [twoStudyData_withArm ginv Fbc hab hcb M _ hβ,
    twoStudyData_withArm ginv Fbc hab hcb M _ hev.self_of_nhds]

omit [DecidableEq K] in
include hd hd' hpos hbd hFbc hFs in
/-- **Non identification over the target class.** Under the hypotheses of
`not_pointIdentified_withArm_marginal`, the causal marginal effect `g(E*[Y(b)]) - g(E*[Y(a)])` of
the target populations in `TargetClass` is not point identified from the two study data, the
target baseline and the target covariate law. -/
theorem not_pointIdentified_targetClass_marginal {g : ℝ → ℝ} (hg : ∀ t, g (ginv t) = t)
    (M : MultilevelModel J K p) {jac jbc : J} {a b c : K} (hab : a ≠ b) (hcb : c ≠ b) (αs : ℝ)
    (hS : sensitivity (coefMeanDeriv Fbc ginv' (M.μ jbc) M.β₁ (M.β₂ b, M.γ b))
      (coefMeanDeriv Fs ginv' αs M.β₁ (M.β₂ b, M.γ b)) ≠ 0) :
    ¬PointIdentified (TargetClass (Ω := Fin p → ℝ) J ginv)
      (fun m => (twoStudyData ginv Fbc jac jbc a b c m.2.1, m.2.2, m.1.covLaw))
      (fun m => m.1.marginalEffect g a b) := by
  classical
  obtain ⟨φ, h0, hev, hφ⟩ := exists_withArm_level_curve hd hd' hpos hbd hFbc M b jbc
  refine not_pointIdentified_of_hasFDerivAt
    (c := fun β => (surfacePopulation Fs (M.withArm b (β, φ β)) ginv αs, M.withArm b (β, φ β), αs))
    (fun β => surfacePopulation_mem_targetClass hd hbd hFs _ _) ?_
    (hasFDerivAt_targetMarginal_along hd hd' hpos hbd hFs hg M hab αs h0 hφ)
    (smul_ne_zero (inv_ne_zero (hpos _).ne') hS)
  filter_upwards [hev] with β hβ
  refine Prod.ext ?_ (Prod.ext rfl rfl)
  change twoStudyData ginv Fbc jac jbc a b c (M.withArm b (β, φ β)) =
    twoStudyData ginv Fbc jac jbc a b c (M.withArm b (M.β₂ b, φ (M.β₂ b)))
  rw [twoStudyData_withArm ginv Fbc hab hcb M _ hβ,
    twoStudyData_withArm ginv Fbc hab hcb M _ hev.self_of_nhds]

include hd hd' hpos hbd hFbc in
/-- **Non identification of the conditional effect at a covariate value.** In the two study
network, let `g` invert `g⁻¹`. The conditional effect `g(m_b(x₀)) - g(m_a(x₀))` at the target
baseline `α*` moves along the level curve with derivative `v ↦ (x₀ - x̃)ᵀ v`, where `x̃` is the
tilted covariate mean of the aggregate study; so if `x₀ ≠ x̃` it is not point identified from the
data, even among the models that differ from `M` only in `(β₂,b, γ_b)`. -/
theorem withArm_conditional_not_identified {g : ℝ → ℝ} (hg : ∀ t, g (ginv t) = t)
    (M : MultilevelModel J K p) {jac jbc : J} {a b c : K} (hab : a ≠ b) (hcb : c ≠ b) (αs : ℝ)
    (x₀ : Fin p → ℝ) (hx : x₀ ≠ tiltedMean Fbc ginv' (M.μ jbc) M.β₁ (M.β₂ b, M.γ b)) :
    ¬PointIdentified (Set.range (M.withArm b)) (twoStudyData ginv Fbc jac jbc a b c)
      (fun N => linkContrast g (N.surface ginv αs a) (N.surface ginv αs b) x₀) := by
  obtain ⟨φ, h0, hev, hφ⟩ := exists_withArm_level_curve hd hd' hpos hbd hFbc M b jbc
  have e : (fun β => linkContrast g ((M.withArm b (β, φ β)).surface ginv αs a)
      ((M.withArm b (β, φ β)).surface ginv αs b) x₀) =
      fun β => coefPred αs M.β₁ x₀ (β, φ β) - M.eta αs a x₀ := by
    funext β
    rw [linkContrast, surface_withArm_of_ne ginv M hab]
    simp only [surface, hg, eta_withArm]
  have hder := ((hasFDerivAt_coefPred αs M.β₁ x₀ (M.β₂ b, φ (M.β₂ b))).comp (M.β₂ b)
    ((hasFDerivAt_id (M.β₂ b)).prodMk hφ))
  refine not_pointIdentified_of_hasFDerivAt (c := fun β => M.withArm b (β, φ β))
    (fun β => ⟨_, rfl⟩) ?_ (by rw [e]; exact (hasFDerivAt_sub_const_iff _).2 hder)
    ((sensitivity_coefDir_ne_zero_iff hd' hpos hbd hFbc _ x₀).2 hx)
  filter_upwards [hev] with β hβ
  rw [twoStudyData_withArm ginv Fbc hab hcb M _ hβ,
    twoStudyData_withArm ginv Fbc hab hcb M _ hev.self_of_nhds]

end Curve

/-! ### The identity link -/

section Identity

variable {Fbc Fs : Measure (Fin p → ℝ)} [IsProbabilityMeasure Fbc] [IsProbabilityMeasure Fs]
  (hFbc : ∀ i, Integrable (fun x : Fin p → ℝ => x i) Fbc)
  (hFs : ∀ i, Integrable (fun x : Fin p → ℝ => x i) Fs)

include hFbc hFs in
/-- **Identity link: a covariate shift breaks identification of the target effect.** Under the
identity link the sensitivity is `x̄* - x̄_bc`; so if the target covariate mean differs from the
covariate mean of the aggregate study, the target mean difference `E*[m_b] - E*[m_a]` is not
point identified from the two study data. -/
theorem identity_marginal_not_identified (M : MultilevelModel J K p) {jac jbc : J} {a b c : K}
    (hab : a ≠ b) (hcb : c ≠ b) (αs : ℝ) (hcov : covMean Fs ≠ covMean Fbc) :
    ¬PointIdentified (Set.range (M.withArm b)) (twoStudyData id Fbc jac jbc a b c)
      (fun N => linkMarginal id Fs (N.surface id αs a) (N.surface id αs b)) :=
  not_pointIdentified_withArm_marginal (ginv' := fun _ => 1) (C := 1) hasDerivAt_id
    continuous_const (fun _ => one_pos) (fun _ => by norm_num) hFbc hFs (fun _ => rfl) M hab hcb
    αs ((sensitivity_ne_zero_iff continuous_const (fun _ => one_pos) (C := 1)
      (fun _ => by norm_num) hFbc hFs _).2 (by rwa [tiltedMean_one, tiltedMean_one]))

include hFbc in
/-- **Identity link: the conditional effect at `x₀` is not identified when `x₀ ≠ x̄_bc`.** -/
theorem identity_conditional_not_identified (M : MultilevelModel J K p) {jac jbc : J}
    {a b c : K} (hab : a ≠ b) (hcb : c ≠ b) (αs : ℝ) (x₀ : Fin p → ℝ) (hx : x₀ ≠ covMean Fbc) :
    ¬PointIdentified (Set.range (M.withArm b)) (twoStudyData id Fbc jac jbc a b c)
      (fun N => linkContrast id (N.surface id αs a) (N.surface id αs b) x₀) :=
  withArm_conditional_not_identified (ginv' := fun _ => 1) (C := 1) hasDerivAt_id
    continuous_const (fun _ => one_pos) (fun _ => by norm_num) hFbc (fun _ => rfl) M hab hcb αs
    x₀ (by rwa [tiltedMean_one])

end Identity

end MultilevelModel

/-! ### Instances -/

open MultilevelModel

theorem covMean_binaryLaw {q : ℝ} (hq : q ∈ Set.Icc (0 : ℝ) 1) :
    covMean (binaryLaw q) = fun _ => q := by
  funext i
  rw [covMean, integral_binaryLaw hq]
  ring

/-- **An instance of the identity link results**: in the triangle model with all parameters
zero, aggregate covariate law `binaryLaw (1/2)` and target covariate law `binaryLaw (1/4)`, neither
the target mean difference of `b` against `a` nor the conditional effect at `x₀ = 0` is point
identified from the two study data. -/
theorem identity_not_identified_instance :
    ¬PointIdentified (Set.range ((triangleModel 0 0 0 0 0 0 0).withArm 1))
        (twoStudyData id (binaryLaw (1 / 2)) 0 1 0 1 2)
        (fun N => linkMarginal id (binaryLaw (1 / 4)) (N.surface id 0 0) (N.surface id 0 1)) ∧
      ¬PointIdentified (Set.range ((triangleModel 0 0 0 0 0 0 0).withArm 1))
        (twoStudyData id (binaryLaw (1 / 2)) 0 1 0 1 2)
        (fun N => linkContrast id (N.surface id 0 0) (N.surface id 0 1) 0) := by
  have hq2 : (1 / 2 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := ⟨by norm_num, by norm_num⟩
  have hq4 : (1 / 4 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := ⟨by norm_num, by norm_num⟩
  have := isProbabilityMeasure_binaryLaw hq2
  have := isProbabilityMeasure_binaryLaw hq4
  refine ⟨identity_marginal_not_identified (fun _ => integrable_binaryLaw _ _)
    (fun _ => integrable_binaryLaw _ _) _ (by decide) (by decide) 0 ?_,
    identity_conditional_not_identified (fun _ => integrable_binaryLaw _ _) _ (by decide)
      (by decide) 0 0 ?_⟩
  · rw [covMean_binaryLaw hq2, covMean_binaryLaw hq4]
    intro h
    have := congrFun h 0
    norm_num at this
  · rw [covMean_binaryLaw hq2]
    intro h
    have := congrFun h 0
    norm_num at this

/-- **An instance of the smooth global graph**: with the logit link and `binaryLaw (1/2)`, the
parameters `(β₂,b, γ_b)` of `b` with aggregate mean `1/2` form the graph of a continuously
differentiable function. -/
theorem logit_solution_graph_instance :
    ∃ Γ : (Fin 1 → ℝ) → ℝ, ContDiff ℝ 1 Γ ∧
      ∀ w, ((triangleModel 0 0 0 0 0 0 0).withArm 1 w).armMean Real.sigmoid 0
        (binaryLaw (1 / 2)) 1 = 1 / 2 ↔ w.2 = Γ w.1 := by
  have : IsProbabilityMeasure (binaryLaw (1 / 2)) :=
    isProbabilityMeasure_binaryLaw ⟨by norm_num, by norm_num⟩
  obtain ⟨Γ, hΓ, hiff, -⟩ := contDiff_withArm_solution_graph
    (F := binaryLaw (1 / 2)) (ginv' := sigmoidDeriv1) (C := 1)
    (fun t => Real.hasDerivAt_sigmoid t) continuous_sigmoidD1 sigmoidDeriv1_pos abs_sigmoidD1_le
    (fun _ => integrable_binaryLaw _ _) (triangleModel 0 0 0 0 0 0 0) 1 0
    (θ := 1 / 2) ⟨0, by simp [Real.sigmoid_zero]⟩
  exact ⟨Γ, hΓ, hiff⟩

end NetworkMetaRegression

end CausalInference
