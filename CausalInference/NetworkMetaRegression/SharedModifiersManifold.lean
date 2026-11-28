/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.NetworkMetaRegression.SharedModifiersNecessary
public import Mathlib.Analysis.Calculus.ImplicitFunction.ProdDomain
public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.Analysis.Calculus.MeanValue

/-!
# The solution set of an aggregate mean equation

In the two study network of `IdentifiabilityTwoStudy.lean` without shared effect modifiers, the
parameters `w = (β₂,b, γ_b) ∈ ℝ^p × ℝ` of treatment `b` enter the data only through the
aggregate mean of arm `b` in the aggregate study,
`Θ(w) = ∫ g⁻¹((α + γ_b) + xᵀ(β₁ + β₂,b)) F(dx)` (`coefMean`), with `α = μ_jbc` and `F = F_bc`.
This file describes the set of `w` with `Θ(w) = θ` for an observed mean `θ`.

* **Global graph, no smoothness** (`withArm_solution_graph`): for a continuous strictly
  increasing inverse link and `θ` in its range, for every `β₂,b` exactly one `γ_b` solves the
  equation, so the solution set is the graph of a function `γ_b = Γ(β₂,b)`
  (`existsUnique_shiftMean_eq`).
* **Differentiation under the integral** (`hasStrictFDerivAt_coefMean`): if `g⁻¹` has a
  continuous derivative `g⁻¹'` bounded by `C` and the covariates are integrable under `F`, then
  `Θ` is strictly differentiable with derivative `v ↦ E[g⁻¹'(η)(xᵀv₁ + v₂)]`. Bounded derivative
  and integrable covariates give the integrable dominating function `C (∑ |x_i| + 1)`; they
  also give the integrability of `g⁻¹(η)` (`integrable_inv_link_affine`), since `g⁻¹` is then
  Lipschitz.
* **The implicit function** (`coefMean_implicit`): if moreover `g⁻¹' > 0`, then near every
  parameter `w₀` the level set of `Θ` through `w₀` is the graph of a differentiable function with
  gradient `-E[g⁻¹'(η) X] / E[g⁻¹'(η)]`, by `HasStrictFDerivAt.implicitFunctionOfProdDomain`.
* **The smooth global graph** (`contDiff_withArm_solution_graph`): the function `Γ` of the
  global graph is continuously differentiable with that gradient at every point.

## Main definitions

* `MultilevelModel.withArm M k w`: the model `M` with `(β₂,k, γ_k)` replaced by `w`.
* `coefDir x`, `coefPred`, `coefMean`, `coefMeanDeriv`, `implicitGrad`.
-/

@[expose] public section

namespace CausalInference

namespace NetworkMetaRegression

open MeasureTheory Filter Topology Set

variable {p : ℕ}

/-! ### The arm mean as a function of the parameters of one arm -/

/-- The derivative `L_x(v) = xᵀv₁ + v₂` of the linear predictor in the parameters
`(β₂,k, γ_k)`. -/
noncomputable def coefDir (x : Fin p → ℝ) : (Fin p → ℝ) × ℝ →L[ℝ] ℝ :=
  (∑ i, x i • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin p => ℝ) i).comp
      (ContinuousLinearMap.fst ℝ (Fin p → ℝ) ℝ) +
    ContinuousLinearMap.snd ℝ (Fin p → ℝ) ℝ

theorem coefDir_apply (x : Fin p → ℝ) (v : (Fin p → ℝ) × ℝ) : coefDir x v = x ⬝ᵥ v.1 + v.2 := by
  simp [coefDir, dotProduct]

theorem continuous_coefDir : Continuous (coefDir (p := p)) := by
  unfold coefDir
  exact ((continuous_finsetSum _ fun i _ => (continuous_apply i).smul continuous_const).clm_comp
    continuous_const).add continuous_const

theorem norm_coefDir_le (x : Fin p → ℝ) : ‖coefDir x‖ ≤ ∑ i, |x i| + 1 := by
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun v => ?_
  rw [coefDir_apply, add_mul, one_mul, Real.norm_eq_abs]
  refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
  · rw [dotProduct, Finset.sum_mul]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
    rw [abs_mul]
    refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
    have := (norm_le_pi_norm v.1 i).trans (norm_fst_le v)
    rwa [Real.norm_eq_abs] at this
  · have := norm_snd_le v
    rwa [Real.norm_eq_abs] at this

/-- The linear predictor `(α + γ) + xᵀ(β₁ + β)` at the parameters `w = (β, γ)` of one arm, with
baseline `α` and prognostic effect `β₁`. -/
def coefPred (α : ℝ) (β₁ x : Fin p → ℝ) (w : (Fin p → ℝ) × ℝ) : ℝ :=
  (α + w.2) + x ⬝ᵥ (β₁ + w.1)

theorem hasFDerivAt_coefPred (α : ℝ) (β₁ x : Fin p → ℝ) (w : (Fin p → ℝ) × ℝ) :
    HasFDerivAt (coefPred α β₁ x) (coefDir x) w := by
  have : coefPred α β₁ x = fun w => (α + x ⬝ᵥ β₁) + coefDir x w := by
    funext w; simp only [coefPred, coefDir_apply, dotProduct_add]; ring
  rw [this]
  exact (coefDir x).hasFDerivAt.const_add _

theorem continuous_coefPred (α : ℝ) (β₁ : Fin p → ℝ) (w : (Fin p → ℝ) × ℝ) :
    Continuous fun x => coefPred α β₁ x w := by
  unfold coefPred dotProduct; fun_prop

theorem continuous_coefPred_param (α : ℝ) (β₁ x : Fin p → ℝ) : Continuous (coefPred α β₁ x) :=
  continuous_iff_continuousAt.2 fun w => (hasFDerivAt_coefPred α β₁ x w).continuousAt

/-- The aggregate mean `Θ(w) = ∫ g⁻¹((α + γ) + xᵀ(β₁ + β)) F(dx)` as a function of the
parameters `w = (β, γ)` of one arm. -/
noncomputable def coefMean (F : Measure (Fin p → ℝ)) (ginv : ℝ → ℝ) (α : ℝ) (β₁ : Fin p → ℝ)
    (w : (Fin p → ℝ) × ℝ) : ℝ :=
  ∫ x, ginv (coefPred α β₁ x w) ∂F

/-- The derivative `DΘ(w) = ∫ g⁻¹'(η_w(x)) L_x F(dx)` of the aggregate mean in the parameters. -/
noncomputable def coefMeanDeriv (F : Measure (Fin p → ℝ)) (ginv' : ℝ → ℝ) (α : ℝ)
    (β₁ : Fin p → ℝ) (w : (Fin p → ℝ) × ℝ) : (Fin p → ℝ) × ℝ →L[ℝ] ℝ :=
  ∫ x, ginv' (coefPred α β₁ x w) • coefDir x ∂F

theorem coefMean_eq_shiftMean (F : Measure (Fin p → ℝ)) (ginv : ℝ → ℝ) (α : ℝ)
    (β₁ : Fin p → ℝ) (w : (Fin p → ℝ) × ℝ) :
    coefMean F ginv α β₁ w = shiftMean F ginv (fun x => x ⬝ᵥ (β₁ + w.1)) (α + w.2) :=
  rfl

/-! ### Bounded derivative and integrable covariates -/

section Bounded

variable {F : Measure (Fin p → ℝ)} {ginv ginv' : ℝ → ℝ} {C : ℝ}

/-- `∑ |x_i| + 1` is integrable under a finite law with integrable coordinates. -/
theorem integrable_sum_abs_add_one [IsFiniteMeasure F]
    (hF : ∀ i, Integrable (fun x : Fin p → ℝ => x i) F) :
    Integrable (fun x : Fin p → ℝ => ∑ i, |x i| + 1) F :=
  (integrable_finsetSum _ fun i _ => (hF i).abs).add (integrable_const _)

/-- **A Lipschitz inverse link has integrable aggregate integrands.** If `g⁻¹` has a derivative
bounded by `C`, then `g⁻¹(c + xᵀb)` is integrable under every finite law with integrable
coordinates. -/
theorem integrable_inv_link_affine [IsFiniteMeasure F] (hd : ∀ t, HasDerivAt ginv (ginv' t) t)
    (hbd : ∀ t, |ginv' t| ≤ C) (hF : ∀ i, Integrable (fun x : Fin p → ℝ => x i) F) (c : ℝ)
    (b : Fin p → ℝ) : Integrable (fun x => ginv (c + x ⬝ᵥ b)) F := by
  have hcont : Continuous ginv := continuous_iff_continuousAt.2 fun t => (hd t).continuousAt
  have hlip : ∀ s, |ginv s| ≤ |ginv 0| + C * |s| := fun s => by
    have := convex_univ.norm_image_sub_le_of_norm_hasDerivWithin_le (f := ginv)
      (fun t _ => (hd t).hasDerivWithinAt) (fun t _ => by rw [Real.norm_eq_abs]; exact hbd t)
      (mem_univ 0) (mem_univ s)
    simp only [Real.norm_eq_abs, sub_zero] at this
    linarith [abs_sub_abs_le_abs_sub (ginv s) (ginv 0)]
  have hC : 0 ≤ C := (abs_nonneg _).trans (hbd 0)
  have hdot : ∀ x : Fin p → ℝ, |x ⬝ᵥ b| ≤ ∑ i, |x i| * |b i| := fun x => by
    rw [dotProduct]
    exact (Finset.abs_sum_le_sum_abs _ _).trans (le_of_eq (by simp [abs_mul]))
  refine ((integrable_const |ginv 0|).add (((integrable_const |c|).add
    (integrable_finsetSum Finset.univ fun i _ => (hF i).abs.mul_const |b i|)).const_mul C)).mono'
    (hcont.comp (by unfold dotProduct; fun_prop)).aestronglyMeasurable (ae_of_all _ fun x => ?_)
  rw [Real.norm_eq_abs]
  have h1 := hlip (c + x ⬝ᵥ b)
  have h2 : |c + x ⬝ᵥ b| ≤ |c| + ∑ i, |x i| * |b i| := (abs_add_le _ _).trans (by linarith [hdot x])
  have h3 := mul_le_mul_of_nonneg_left h2 hC
  simp only [Pi.add_apply]
  linarith

variable (hd : ∀ t, HasDerivAt ginv (ginv' t) t) (hd' : Continuous ginv')
  (hbd : ∀ t, |ginv' t| ≤ C) (hF : ∀ i, Integrable (fun x : Fin p → ℝ => x i) F)
  {α : ℝ} {β₁ : Fin p → ℝ}
include hd' hbd hF

theorem integrable_coefMeanDeriv_integrand [IsFiniteMeasure F] (w : (Fin p → ℝ) × ℝ) :
    Integrable (fun x => ginv' (coefPred α β₁ x w) • coefDir x) F := by
  refine ((integrable_sum_abs_add_one hF).const_mul C).mono'
    ((hd'.comp (continuous_coefPred α β₁ w)).smul continuous_coefDir).aestronglyMeasurable
    (ae_of_all _ fun x => ?_)
  rw [norm_smul, Real.norm_eq_abs]
  exact mul_le_mul (hbd _) (norm_coefDir_le x) (norm_nonneg _) ((abs_nonneg _).trans (hbd 0))

/-- `DΘ(w)(v) = E[g⁻¹'(η_w)(xᵀv₁ + v₂)]`. -/
theorem coefMeanDeriv_apply [IsFiniteMeasure F] (w v : (Fin p → ℝ) × ℝ) :
    coefMeanDeriv F ginv' α β₁ w v = ∫ x, ginv' (coefPred α β₁ x w) * (x ⬝ᵥ v.1 + v.2) ∂F := by
  rw [coefMeanDeriv, ContinuousLinearMap.integral_apply
    (integrable_coefMeanDeriv_integrand hd' hbd hF w)]
  simp [coefDir_apply]

/-- The partial derivative in `γ`: `E[g⁻¹'(η_w)]`. -/
theorem coefMeanDeriv_snd [IsFiniteMeasure F] (w : (Fin p → ℝ) × ℝ) :
    coefMeanDeriv F ginv' α β₁ w (0, 1) = ∫ x, ginv' (coefPred α β₁ x w) ∂F := by
  rw [coefMeanDeriv_apply hd' hbd hF]; simp

/-- The partial derivative in `β_i`: `E[g⁻¹'(η_w) X_i]`. -/
theorem coefMeanDeriv_fst [IsFiniteMeasure F] (w : (Fin p → ℝ) × ℝ) (i : Fin p) :
    coefMeanDeriv F ginv' α β₁ w (Pi.single i 1, 0) =
      ∫ x, ginv' (coefPred α β₁ x w) * x i ∂F := by
  rw [coefMeanDeriv_apply hd' hbd hF]; simp [dotProduct_single]

theorem integrable_inv_link_deriv [IsFiniteMeasure F] (w : (Fin p → ℝ) × ℝ) :
    Integrable (fun x => ginv' (coefPred α β₁ x w)) F := by
  have := (ContinuousLinearMap.apply ℝ ℝ ((0 : Fin p → ℝ), (1 : ℝ))).integrable_comp
    (integrable_coefMeanDeriv_integrand hd' hbd hF (α := α) (β₁ := β₁) w)
  simpa [coefDir_apply] using this

/-- The partial derivative in `γ` is positive when `g⁻¹' > 0`. -/
theorem coefMeanDeriv_snd_pos [IsProbabilityMeasure F] (hpos : ∀ t, 0 < ginv' t)
    (w : (Fin p → ℝ) × ℝ) : 0 < coefMeanDeriv F ginv' α β₁ w (0, 1) := by
  rw [coefMeanDeriv_snd hd' hbd hF]
  exact integral_pos_of_forall_pos (integrable_inv_link_deriv hd' hbd hF w) fun _ => hpos _

include hd in
/-- **Differentiation under the integral**: `Θ` has the derivative `DΘ(w)` at every `w`. -/
theorem hasFDerivAt_coefMean [IsFiniteMeasure F] (w₀ : (Fin p → ℝ) × ℝ) :
    HasFDerivAt (coefMean F ginv α β₁) (coefMeanDeriv F ginv' α β₁ w₀) w₀ := by
  have hcont : Continuous ginv := continuous_iff_continuousAt.2 fun t => (hd t).continuousAt
  refine hasFDerivAt_integral_of_dominated_of_fderiv_le (F := fun w x => ginv (coefPred α β₁ x w))
    (F' := fun w x => ginv' (coefPred α β₁ x w) • coefDir x)
    (bound := fun x => C * (∑ i, |x i| + 1))
    univ_mem
    (Eventually.of_forall fun w => (hcont.comp (continuous_coefPred α β₁ w)).aestronglyMeasurable)
    (integrable_inv_link_affine hd hbd hF _ _)
    (integrable_coefMeanDeriv_integrand hd' hbd hF w₀).aestronglyMeasurable
    (ae_of_all _ fun x w _ => ?_) ((integrable_sum_abs_add_one hF).const_mul C)
    (ae_of_all _ fun x w _ => (hd _).comp_hasFDerivAt w (hasFDerivAt_coefPred α β₁ x w))
  rw [norm_smul, Real.norm_eq_abs]
  exact mul_le_mul (hbd _) (norm_coefDir_le x) (norm_nonneg _) ((abs_nonneg _).trans (hbd 0))

/-- The derivative `DΘ` is continuous in the parameters, by dominated convergence. -/
theorem continuous_coefMeanDeriv [IsFiniteMeasure F] :
    Continuous (coefMeanDeriv F ginv' α β₁) := by
  refine continuous_iff_continuousAt.2 fun w₀ => continuousAt_of_dominated
    (bound := fun x => C * (∑ i, |x i| + 1))
    (Eventually.of_forall fun w =>
      (integrable_coefMeanDeriv_integrand hd' hbd hF w).aestronglyMeasurable)
    (Eventually.of_forall fun w => ae_of_all _ fun x => ?_)
    ((integrable_sum_abs_add_one hF).const_mul C)
    (ae_of_all _ fun x => ((hd'.comp (continuous_coefPred_param α β₁ x)).smul
      continuous_const).continuousAt)
  rw [norm_smul, Real.norm_eq_abs]
  exact mul_le_mul (hbd _) (norm_coefDir_le x) (norm_nonneg _) ((abs_nonneg _).trans (hbd 0))

include hd in
/-- **`Θ` is strictly differentiable**: it is differentiable everywhere with a continuous
derivative. -/
theorem hasStrictFDerivAt_coefMean [IsFiniteMeasure F] (w₀ : (Fin p → ℝ) × ℝ) :
    HasStrictFDerivAt (coefMean F ginv α β₁) (coefMeanDeriv F ginv' α β₁ w₀) w₀ :=
  hasStrictFDerivAt_of_hasFDerivAt_of_continuousAt
    (Eventually.of_forall fun w => hasFDerivAt_coefMean hd hd' hbd hF w)
    (continuous_coefMeanDeriv hd' hbd hF).continuousAt

end Bounded

/-! ### The implicit function -/

/-- A linear functional on `ℝ^p × ℝ` splits as `D(v, t) = D(v, 0) + t D(0, 1)`. -/
theorem clm_prod_apply_eq_add (D : (Fin p → ℝ) × ℝ →L[ℝ] ℝ) (v : Fin p → ℝ) (t : ℝ) :
    D (v, t) = D (v, 0) + t * D (0, 1) := by
  have : ((v, t) : (Fin p → ℝ) × ℝ) = (v, 0) + t • ((0 : Fin p → ℝ), (1 : ℝ)) := by
    ext <;> simp
  rw [this, map_add, map_smul, smul_eq_mul]

/-- The **implicit gradient** `v ↦ -D(v, 0) / D(0, 1)` of a level set of a function with
derivative `D`. -/
noncomputable def implicitGrad (D : (Fin p → ℝ) × ℝ →L[ℝ] ℝ) : (Fin p → ℝ) →L[ℝ] ℝ :=
  -(D (0, 1))⁻¹ • D.comp (ContinuousLinearMap.inl ℝ (Fin p → ℝ) ℝ)

/-- For `D(0, 1) ≠ 0`, the implicit gradient is `v ↦ -D(v, 0) / D(0, 1)`. -/
theorem implicitGrad_apply (D : (Fin p → ℝ) × ℝ →L[ℝ] ℝ) (_hD : D (0, 1) ≠ 0) (v : Fin p → ℝ) :
    implicitGrad D v = -D (v, 0) / D (0, 1) := by
  simp [implicitGrad, div_eq_inv_mul]

section Implicit

variable {F : Measure (Fin p → ℝ)} [IsProbabilityMeasure F] {ginv ginv' : ℝ → ℝ} {C : ℝ}
  (hd : ∀ t, HasDerivAt ginv (ginv' t) t) (hd' : Continuous ginv') (hpos : ∀ t, 0 < ginv' t)
  (hbd : ∀ t, |ginv' t| ≤ C) (hF : ∀ i, Integrable (fun x : Fin p → ℝ => x i) F)
  {α : ℝ} {β₁ : Fin p → ℝ}
include hd hd' hpos hbd hF

/-- **The implicit function theorem for the aggregate mean equation.** Near every
`w₀ = (β₀, γ₀)` there is a function `φ` with `φ(β₀) = γ₀`, `Θ(β, φ(β)) = Θ(w₀)` for `β` near
`β₀`, and gradient `-DΘ(·, 0) / DΘ(0, 1)` at `β₀`. -/
theorem coefMean_implicit (β₀ : Fin p → ℝ) (γ₀ : ℝ) :
    ∃ φ : (Fin p → ℝ) → ℝ, φ β₀ = γ₀ ∧
      (∀ᶠ β in 𝓝 β₀, coefMean F ginv α β₁ (β, φ β) = coefMean F ginv α β₁ (β₀, γ₀)) ∧
      HasFDerivAt φ (implicitGrad (coefMeanDeriv F ginv' α β₁ (β₀, γ₀))) β₀ := by
  set D := coefMeanDeriv F ginv' α β₁ (β₀, γ₀)
  have hD := hasStrictFDerivAt_coefMean hd hd' hbd hF (α := α) (β₁ := β₁) (β₀, γ₀)
  have hc : 0 < D (0, 1) := coefMeanDeriv_snd_pos hd' hbd hF hpos _
  have hinv : (D ∘L ContinuousLinearMap.inr ℝ (Fin p → ℝ) ℝ).IsInvertible :=
    ⟨ContinuousLinearEquiv.unitsEquivAut ℝ (Units.mk0 _ hc.ne'),
      ContinuousLinearMap.ext_ring (by simp)⟩
  set φ := hD.implicitFunctionOfProdDomain hinv
  have hφ0 : φ β₀ = γ₀ :=
    ((hD.eventually_apply_eq_iff_implicitFunctionOfProdDomain hinv).self_of_nhds).1 rfl
  have hev := hD.eventually_apply_implicitFunctionOfProdDomain hinv
  obtain ⟨φ', hφ'⟩ : ∃ φ', HasFDerivAt φ φ' β₀ :=
    ⟨_, (hD.hasStrictFDerivAt_implicitFunctionOfProdDomain hinv).hasFDerivAt⟩
  have hD' : HasFDerivAt (coefMean F ginv α β₁) D (β₀, φ β₀) := by
    rw [hφ0]; exact hD.hasFDerivAt
  have hcomp := hD'.comp β₀ ((hasFDerivAt_id β₀).prodMk hφ')
  have hconst : HasFDerivAt (fun β => coefMean F ginv α β₁ (β, φ β))
      (0 : (Fin p → ℝ) →L[ℝ] ℝ) β₀ :=
    (hasFDerivAt_const _ β₀).congr_of_eventuallyEq hev
  have hzero := hcomp.unique hconst
  refine ⟨φ, hφ0, hev, ?_⟩
  convert hφ' using 1
  ext v
  have := congrArg (fun L : (Fin p → ℝ) →L[ℝ] ℝ => L v) hzero
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply,
    ContinuousLinearMap.id_apply, zero_apply] at this
  rw [clm_prod_apply_eq_add] at this
  rw [implicitGrad_apply _ hc.ne']
  field_simp
  linarith

end Implicit

/-! ### The model with the parameters of one arm replaced -/

namespace MultilevelModel

variable {J K : Type*} [DecidableEq K]

/-- The model `M` with the interactions and the effect of treatment `k` replaced by
`w = (β₂,k, γ_k)`; every other parameter is kept. -/
def withArm (M : MultilevelModel J K p) (k : K) (w : (Fin p → ℝ) × ℝ) : MultilevelModel J K p :=
  { M with γ := Function.update M.γ k w.2, β₂ := Function.update M.β₂ k w.1 }

theorem withArm_self (M : MultilevelModel J K p) (k : K) : M.withArm k (M.β₂ k, M.γ k) = M := by
  ext <;> simp [withArm]

/-- The predictor of arm `k` of `M.withArm k w` is `coefPred α β₁ x w`. -/
theorem eta_withArm (M : MultilevelModel J K p) (k : K) (w : (Fin p → ℝ) × ℝ) (α : ℝ)
    (x : Fin p → ℝ) : (M.withArm k w).eta α k x = coefPred α M.β₁ x w := by
  simp [eta_eq_affine, withArm, coefPred]

/-- The aggregate mean of arm `k` of `M.withArm k w` is `Θ(w)`. -/
theorem armMean_withArm (ginv : ℝ → ℝ) (M : MultilevelModel J K p) (k : K)
    (w : (Fin p → ℝ) × ℝ) (α : ℝ) (F : Measure (Fin p → ℝ)) :
    (M.withArm k w).armMean ginv α F k = coefMean F ginv α M.β₁ w := by
  simp only [armMean, surface, eta_withArm, coefMean]

/-- The surfaces of the other treatments do not depend on `w`. -/
theorem surface_withArm_of_ne (ginv : ℝ → ℝ) (M : MultilevelModel J K p) {k t : K} (ht : t ≠ k)
    (w : (Fin p → ℝ) × ℝ) (α : ℝ) : (M.withArm k w).surface ginv α t = M.surface ginv α t := by
  funext x
  simp [surface, eta, withArm, NetworkMetaAnalysis.metaRegressionPredictor,
    Function.update_of_ne ht]

theorem withArm_β₁ (M : MultilevelModel J K p) (k : K) (w : (Fin p → ℝ) × ℝ) :
    (M.withArm k w).β₁ = M.β₁ :=
  rfl

theorem withArm_μ (M : MultilevelModel J K p) (k : K) (w : (Fin p → ℝ) × ℝ) :
    (M.withArm k w).μ = M.μ :=
  rfl

variable {F : Measure (Fin p → ℝ)} [IsProbabilityMeasure F] {ginv : ℝ → ℝ}

/-- **The solution set is a global graph, without smoothness.** For a continuous strictly
increasing inverse link, a probability law `F` under which every `g⁻¹(c + xᵀ(β₁ + β))` is
integrable, and an observed mean `θ` in the range of `g⁻¹`, there is a function `Γ` such that the
parameters `w = (β₂,k, γ_k)` with aggregate mean `θ` of arm `k` at baseline `α` are exactly the
`w` with `γ_k = Γ(β₂,k)`: for every `β₂,k` exactly one `γ_k` solves the equation. -/
theorem withArm_solution_graph (hmono : StrictMono ginv) (hcont : Continuous ginv)
    (M : MultilevelModel J K p) (k : K) (α : ℝ)
    (hint : ∀ (β : Fin p → ℝ) (c : ℝ), Integrable (fun x => ginv (c + x ⬝ᵥ (M.β₁ + β))) F)
    {θ : ℝ} (hθ : θ ∈ Set.range ginv) :
    ∃ Γ : (Fin p → ℝ) → ℝ, ∀ w, (M.withArm k w).armMean ginv α F k = θ ↔ w.2 = Γ w.1 := by
  have hdot : ∀ β : Fin p → ℝ, Measurable fun x : Fin p → ℝ => x ⬝ᵥ (M.β₁ + β) := fun β =>
    (by unfold dotProduct; fun_prop : Continuous fun x : Fin p → ℝ => x ⬝ᵥ (M.β₁ + β)).measurable
  choose c hc hcu using fun β : Fin p → ℝ =>
    existsUnique_shiftMean_eq (F := F) hmono hcont (hdot β) (hint β) hθ
  refine ⟨fun β => c β - α, fun w => ?_⟩
  rw [armMean_withArm, coefMean_eq_shiftMean]
  constructor
  · intro h
    have := hcu w.1 _ h
    simp only
    linarith
  · intro h
    simp only at h
    rw [h, show α + (c w.1 - α) = c w.1 by ring]
    exact hc w.1

/-- **The solution set is the graph of a `C¹` function.** Let `g⁻¹` have a continuous, strictly
positive derivative `g⁻¹'` bounded by `C`, let `F` be a probability law with integrable
coordinates, and let `θ` be in the range of `g⁻¹`. Then there is a continuously differentiable
`Γ` such that `(M.withArm k w)` has aggregate mean `θ` of arm `k` exactly when `γ_k = Γ(β₂,k)`,
and at every `β` the gradient of `Γ` is the implicit gradient, with coordinates
`∂Γ/∂β_i = -E[g⁻¹'(η) X_i] / E[g⁻¹'(η)]`, where `η` is the predictor of arm `k` at
`(β, Γ(β))`. -/
theorem contDiff_withArm_solution_graph {ginv' : ℝ → ℝ} {C : ℝ}
    (hd : ∀ t, HasDerivAt ginv (ginv' t) t) (hd' : Continuous ginv') (hpos : ∀ t, 0 < ginv' t)
    (hbd : ∀ t, |ginv' t| ≤ C) (hF : ∀ i, Integrable (fun x : Fin p → ℝ => x i) F)
    (M : MultilevelModel J K p) (k : K) (α : ℝ) {θ : ℝ} (hθ : θ ∈ Set.range ginv) :
    ∃ Γ : (Fin p → ℝ) → ℝ, ContDiff ℝ 1 Γ ∧
      (∀ w, (M.withArm k w).armMean ginv α F k = θ ↔ w.2 = Γ w.1) ∧
      ∀ β, HasFDerivAt Γ (implicitGrad (coefMeanDeriv F ginv' α M.β₁ (β, Γ β))) β ∧
        ∀ i, implicitGrad (coefMeanDeriv F ginv' α M.β₁ (β, Γ β)) (Pi.single i 1) =
          -(∫ x, ginv' ((M.withArm k (β, Γ β)).eta α k x) * x i ∂F) /
            ∫ x, ginv' ((M.withArm k (β, Γ β)).eta α k x) ∂F := by
  have hmono : StrictMono ginv := strictMono_of_hasDerivAt_pos hd hpos
  have hcont : Continuous ginv := continuous_iff_continuousAt.2 fun t => (hd t).continuousAt
  obtain ⟨Γ, hΓ⟩ := withArm_solution_graph hmono hcont M k α
    (fun β c => integrable_inv_link_affine hd hbd hF c _) hθ
  have hiff : ∀ w, coefMean F ginv α M.β₁ w = θ ↔ w.2 = Γ w.1 := fun w => by
    rw [← armMean_withArm ginv M k w α F]; exact hΓ w
  have hder : ∀ β, HasFDerivAt Γ (implicitGrad (coefMeanDeriv F ginv' α M.β₁ (β, Γ β))) β := by
    intro β
    obtain ⟨φ, hφ0, hev, hφ⟩ := coefMean_implicit hd hd' hpos hbd hF (α := α) (β₁ := M.β₁) β (Γ β)
    refine hφ.congr_of_eventuallyEq ?_
    filter_upwards [hev] with b hb
    exact ((hiff (b, φ b)).1 (hb.trans ((hiff _).2 rfl))).symm
  have hΓc : Continuous Γ := continuous_iff_continuousAt.2 fun β => (hder β).continuousAt
  have hDc : Continuous fun β => coefMeanDeriv F ginv' α M.β₁ (β, Γ β) :=
    (continuous_coefMeanDeriv hd' hbd hF).comp (continuous_id.prodMk hΓc)
  refine ⟨Γ, contDiff_one_iff_hasFDerivAt.2 ⟨_, ?_, hder⟩, hΓ, fun β => ⟨hder β, fun i => ?_⟩⟩
  · have hcc : Continuous fun β => coefMeanDeriv F ginv' α M.β₁ (β, Γ β) (0, 1) :=
      hDc.clm_apply continuous_const
    unfold implicitGrad
    exact ((hcc.inv₀ fun β => (coefMeanDeriv_snd_pos hd' hbd hF hpos _).ne').neg.smul
      (hDc.clm_comp continuous_const))
  · rw [implicitGrad_apply _ (coefMeanDeriv_snd_pos hd' hbd hF hpos _).ne',
      coefMeanDeriv_fst hd' hbd hF, coefMeanDeriv_snd hd' hbd hF]
    simp only [eta_withArm]

end MultilevelModel

end NetworkMetaRegression

end CausalInference
