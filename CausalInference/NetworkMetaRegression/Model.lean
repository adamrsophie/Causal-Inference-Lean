/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.PopulationAdjustment.IdentificationFollowUpDesign
public import CausalInference.NetworkMetaAnalysis.MetaRegressionIdentification
public import Mathlib.Probability.Kernel.CompProdEqIff
public import Mathlib.Probability.Kernel.Composition.IntegralCompProd

/-!
# The multilevel network meta-regression model

A network of studies `J` comparing treatments `K`, with `p` covariates. The **individual level
model** of multilevel network meta-regression gives a patient of study `j` on treatment `k` with
covariates `x` the linear predictor

`η_jk(x) = μ_j + xᵀβ₁ + γ_k + xᵀβ₂,k`

(`MultilevelModel.eta`, the predictor `metaRegressionPredictor` of network meta-regression):
study intercepts `μ_j`, prognostic effects `β₁` common to all studies and arms, treatment effects
`γ_k` and treatment by covariate interactions `β₂,k`. The conditional mean of the outcome is
`g⁻¹(η_jk(x))` (`MultilevelModel.surface`) for an inverse link `g⁻¹`.

The **aggregate level model** of a study that reports only arm summaries is the individual model
integrated over the covariate law `F_j` of the study:
`θ_jk = ∫ g⁻¹(η_jk(x)) F_j(dx)` (`MultilevelModel.armMean`). This is a theorem about the outcome,
not a definition: if the outcome given `x` has mean `g⁻¹(η_jk(x))`, the outcome of a patient drawn
from `F_j` has mean `θ_jk` (`integral_snd_compProd_eq_armMean`).

The predictor at an arbitrary baseline `α` is the predictor of the anchored model
`atBaseline α` of `IndirectComparison/AnchoredPredictor.lean` (`eta_eq_predictor`); a study is
the anchored model with its own intercept (`atBaseline_withIntercept`). The shared effect modifier
assumption is the one of that file (`SharedEffectModifiers`), and the treatment class assumption
is the shared effect modifier assumption on every class (`ClassEffectModifiers`).

* **The population free surface** (`linkContrast_surface`, `eta_sub_eta`): on the link scale the
  conditional effect of `b` against `a` is `(γ_b - γ_a) + xᵀ(β₂,b - β₂,a)`, which involves neither
  the baseline nor any covariate law; a change of baseline shifts every link scale predictor by
  the same amount.
* **Individual data determine the surfaces** (`ae_surface_eq_of_compProd_eq`): if the outcome
  family is parameterized by its mean, two models whose joint laws of covariates and outcome
  coincide have almost everywhere equal surfaces.
* **No covariate effects** (`armMean_of_no_covariate_effects`): with `β₁ = 0` and `β₂ = 0` the
  aggregate mean is `g⁻¹(α + γ_k)` for every covariate law, and the marginal effect on the link
  scale is `γ_b - γ_a`: the model reduces to network meta-analysis.

## Main definitions

* `MultilevelModel`, `MultilevelModel.atBaseline`, `MultilevelModel.eta`,
  `MultilevelModel.surface`, `MultilevelModel.armMean`.
* `MultilevelModel.IsAnchoredAt`, `MultilevelModel.SharedEffectModifiers`,
  `MultilevelModel.ClassEffectModifiers`.

## Main results

* `eta_eq_predictor`, `eta_eq_affine`, `eta_sub_eta`, `linkContrast_surface`.
* `integral_snd_compProd_eq_armMean`, `ae_surface_eq_of_compProd_eq`.
* `armMean_of_no_covariate_effects`.

## References

* D. M. Phillippo, S. Dias, A. E. Ades, M. Belger, A. Brnabic, A. Schacht, D. Saure, Z. Kadziola
  and N. J. Welton, *Multilevel network meta-regression for population-adjusted treatment
  comparisons*, Journal of the Royal Statistical Society Series A 183 (2020).
-/

@[expose] public section

namespace CausalInference

namespace NetworkMetaRegression

open MeasureTheory ProbabilityTheory EffectMeasure IndirectComparison NetworkMetaAnalysis

/-- The parameters of the **multilevel network meta-regression model** for studies `J`,
treatments `K` and `p` covariates: study intercepts `μ_j`, prognostic effects `β₁`, treatment
effects `γ_k` and treatment by covariate interactions `β₂,k`. -/
@[ext]
structure MultilevelModel (J K : Type*) (p : ℕ) where
  /-- The study intercepts. -/
  μ : J → ℝ
  /-- The prognostic effects, common to studies and arms. -/
  β₁ : Fin p → ℝ
  /-- The treatment effects. -/
  γ : K → ℝ
  /-- The treatment by covariate interactions. -/
  β₂ : K → Fin p → ℝ

namespace MultilevelModel

variable {J K : Type*} {p : ℕ}

/-- The anchored model of `IndirectComparison/AnchoredPredictor.lean` with the coefficients of
`M` and the baseline `α`: the model of a population with intercept `α`. -/
def atBaseline (M : MultilevelModel J K p) (α : ℝ) : AnchoredModel K p :=
  ⟨α, M.β₁, M.γ, M.β₂⟩

/-- Changing the intercept of an anchored model is changing the baseline. -/
theorem atBaseline_withIntercept (M : MultilevelModel J K p) (α α' : ℝ) :
    (M.atBaseline α).withIntercept α' = M.atBaseline α' :=
  rfl

/-- The **linear predictor** at baseline `α` of treatment `k` and covariates `x`:
`α + xᵀβ₁ + γ_k + xᵀβ₂,k`. The predictor of study `j` is `M.eta (M.μ j)`. -/
def eta (M : MultilevelModel J K p) (α : ℝ) (k : K) (x : Fin p → ℝ) : ℝ :=
  metaRegressionPredictor α M.β₁ M.γ M.β₂ k x

/-- The **conditional mean surface** `g⁻¹(η_k(x))` of treatment `k` at baseline `α`. -/
def surface (ginv : ℝ → ℝ) (M : MultilevelModel J K p) (α : ℝ) (k : K) (x : Fin p → ℝ) : ℝ :=
  ginv (M.eta α k x)

/-- The **aggregate arm mean** `∫ g⁻¹(η_k(x)) F(dx)` of treatment `k` at baseline `α` under the
covariate law `F`; the arm mean of arm `k` of study `j` is `M.armMean ginv (M.μ j) (F j) k`. -/
noncomputable def armMean (ginv : ℝ → ℝ) (M : MultilevelModel J K p) (α : ℝ)
    (F : Measure (Fin p → ℝ)) (k : K) : ℝ :=
  ∫ x, M.surface ginv α k x ∂F

/-- The model is **anchored at** the reference treatment `r`: `γ_r = 0` and `β₂,r = 0`. -/
def IsAnchoredAt (M : MultilevelModel J K p) (r : K) : Prop := M.γ r = 0 ∧ M.β₂ r = 0

/-- The treatments in `S` **share their effect modifiers**: the shared effect modifier
assumption `AnchoredModel.SharedEffectModifiers` of the coefficients (at any baseline). -/
def SharedEffectModifiers (M : MultilevelModel J K p) (S : Set K) : Prop :=
  (M.atBaseline 0).SharedEffectModifiers S

theorem sharedEffectModifiers_iff (M : MultilevelModel J K p) (S : Set K) :
    M.SharedEffectModifiers S ↔ ∀ b ∈ S, ∀ c ∈ S, M.β₂ b = M.β₂ c :=
  Iff.rfl

/-- The shared effect modifier assumption does not depend on the baseline. -/
theorem sharedEffectModifiers_iff_atBaseline (M : MultilevelModel J K p) (S : Set K) (α : ℝ) :
    M.SharedEffectModifiers S ↔ (M.atBaseline α).SharedEffectModifiers S :=
  Iff.rfl

/-- **Treatment class effect modification**: the active treatments (those other than the reference
`r`) of each class `c` of the classification `cls` share their effect modifiers. -/
def ClassEffectModifiers {C : Type*} (M : MultilevelModel J K p) (r : K) (cls : K → C) : Prop :=
  ∀ c, M.SharedEffectModifiers {k | k ≠ r ∧ cls k = c}

theorem classEffectModifiers_iff {C : Type*} (M : MultilevelModel J K p) (r : K) (cls : K → C) :
    M.ClassEffectModifiers r cls ↔
      ∀ k k', k ≠ r → k' ≠ r → cls k = cls k' → M.β₂ k = M.β₂ k' :=
  ⟨fun h k k' hk hk' hc => h (cls k') k ⟨hk, hc⟩ k' ⟨hk', rfl⟩,
    fun h _c b hb d hd => h b d hb.1 hd.1 (hb.2.trans hd.2.symm)⟩

/-! ### The linear predictor -/

/-- The predictor at baseline `α` is the predictor of the anchored model `atBaseline α`. -/
theorem eta_eq_predictor (M : MultilevelModel J K p) (α : ℝ) (k : K) (x : Fin p → ℝ) :
    M.eta α k x = (M.atBaseline α).predictor k x := by
  simp only [eta, metaRegressionPredictor, AnchoredModel.predictor, atBaseline,
    anchoredPredictor, dotProduct]
  ring

/-- **The predictor is affine in the covariates**: `η_k(x) = (α + γ_k) + xᵀ(β₁ + β₂,k)`. -/
theorem eta_eq_affine (M : MultilevelModel J K p) (α : ℝ) (k : K) (x : Fin p → ℝ) :
    M.eta α k x = (α + M.γ k) + x ⬝ᵥ (M.β₁ + M.β₂ k) := by
  simp only [eta, metaRegressionPredictor, dotProduct_add]
  ring

/-- **A change of baseline shifts every predictor by the same amount**. -/
theorem eta_sub_eta (M : MultilevelModel J K p) (α α' : ℝ) (k : K) (x : Fin p → ℝ) :
    M.eta α k x - M.eta α' k x = α - α' := by
  simp only [eta, metaRegressionPredictor]
  ring

theorem continuous_eta (M : MultilevelModel J K p) (α : ℝ) (k : K) : Continuous (M.eta α k) := by
  unfold MultilevelModel.eta metaRegressionPredictor dotProduct
  fun_prop

theorem measurable_surface {ginv : ℝ → ℝ} (hginv : Measurable ginv) (M : MultilevelModel J K p)
    (α : ℝ) (k : K) : Measurable (M.surface ginv α k) :=
  hginv.comp (M.continuous_eta α k).measurable

/-- **The population free surface.** If `g (g⁻¹ y) = y` for every `y`, the conditional effect on
the link scale of `b` against `a` at `x` is `(γ_b - γ_a) + xᵀ(β₂,b - β₂,a)`: it does not involve
the baseline, and it involves no covariate law. -/
theorem linkContrast_surface {g ginv : ℝ → ℝ} (hg : ∀ y, g (ginv y) = y)
    (M : MultilevelModel J K p) (α : ℝ) (a b : K) (x : Fin p → ℝ) :
    linkContrast g (M.surface ginv α a) (M.surface ginv α b) x =
      (M.γ b - M.γ a) + x ⬝ᵥ (M.β₂ b - M.β₂ a) := by
  simp only [linkContrast, surface, hg, eta, metaRegressionPredictor, dotProduct_sub]
  ring

/-- With integrable covariate coordinates the predictor is integrable. -/
theorem integrable_eta {F : Measure (Fin p → ℝ)} [IsFiniteMeasure F]
    (hF : ∀ i, Integrable (fun x : Fin p → ℝ => x i) F) (M : MultilevelModel J K p) (α : ℝ)
    (k : K) : Integrable (M.eta α k) F := by
  have e : M.eta α k = fun x => (α + M.γ k) + ∑ i, x i * (M.β₁ + M.β₂ k) i := by
    funext x
    rw [eta_eq_affine]
    rfl
  rw [e]
  exact (integrable_const _).add (integrable_finsetSum _ fun i _ => (hF i).mul_const _)

/-! ### The aggregate model is the integrated individual model -/

/-- **The aggregate mean is the mean outcome of the arm.** Let the outcome of a patient with
covariates `x` on treatment `k` have the law `κ x`, with mean `g⁻¹(η_k(x))` for almost every `x`
under the covariate law `F` (the individual level model), and let the outcome be integrable under
the joint law `F ⊗ₘ κ`. Then the outcome of a patient drawn from `F` has mean
`θ_k = ∫ g⁻¹(η_k(x)) F(dx)`. -/
theorem integral_snd_compProd_eq_armMean {ginv : ℝ → ℝ} (M : MultilevelModel J K p) (α : ℝ)
    (k : K) {F : Measure (Fin p → ℝ)} [SFinite F] {κ : Kernel (Fin p → ℝ) ℝ} [IsSFiniteKernel κ]
    (hκ : ∀ᵐ x ∂F, ∫ y, y ∂κ x = M.surface ginv α k x)
    (hY : Integrable (fun z : (Fin p → ℝ) × ℝ => z.2) (F ⊗ₘ κ)) :
    ∫ y, y ∂(F ⊗ₘ κ).snd = M.armMean ginv α F k := by
  rw [Measure.snd, integral_map (f := fun y : ℝ => y) measurable_snd.aemeasurable
    measurable_id.aestronglyMeasurable,
    Measure.integral_compProd hY, armMean]
  exact integral_congr_ae hκ

/-- **Individual data determine the surface.** Let the outcome law given covariates `x` be
`π (g⁻¹(η_k(x)))` for an outcome family `π` of probability laws parameterized by their mean
(`∫ y ∂π θ = θ` for every `θ`). If two models give the same joint law of covariates and outcome
under the covariate law `F`, their surfaces agree `F`-almost everywhere. -/
theorem ae_surface_eq_of_compProd_eq {ginv : ℝ → ℝ} {π : ℝ → Measure ℝ}
    (hπ : ∀ θ, ∫ y, y ∂π θ = θ) {M M' : MultilevelModel J K p} {α α' : ℝ} {k k' : K}
    {F : Measure (Fin p → ℝ)} [IsFiniteMeasure F] {κ κ' : Kernel (Fin p → ℝ) ℝ}
    [IsFiniteKernel κ] [IsFiniteKernel κ'] (hκ : ∀ x, κ x = π (M.surface ginv α k x))
    (hκ' : ∀ x, κ' x = π (M'.surface ginv α' k' x)) (h : F ⊗ₘ κ = F ⊗ₘ κ') :
    M.surface ginv α k =ᵐ[F] M'.surface ginv α' k' := by
  filter_upwards [Kernel.ae_eq_of_compProd_eq h] with x hx
  have h1 := hπ (M.surface ginv α k x)
  rw [← hκ x, hx, hκ' x, hπ] at h1
  exact h1.symm

/-! ### No covariate effects -/

/-- **Without covariate effects the model is a network meta-analysis.** If `β₁ = 0` and
`β₂,k = 0` for every `k`, the predictor is `α + γ_k`, the aggregate mean is `g⁻¹(α + γ_k)` under
every probability law of the covariates, and if `g (g⁻¹ y) = y` the marginal effect on the link
scale of `b` against `a` is `γ_b - γ_a`, free of the baseline and of the covariate law. -/
theorem armMean_of_no_covariate_effects {g ginv : ℝ → ℝ} (hg : ∀ y, g (ginv y) = y)
    (M : MultilevelModel J K p) (hβ₁ : M.β₁ = 0) (hβ₂ : ∀ k, M.β₂ k = 0) (α : ℝ)
    (F : Measure (Fin p → ℝ)) [IsProbabilityMeasure F] :
    (∀ k x, M.eta α k x = α + M.γ k) ∧ (∀ k, M.armMean ginv α F k = ginv (α + M.γ k)) ∧
      ∀ a b, linkMarginal g F (M.surface ginv α a) (M.surface ginv α b) = M.γ b - M.γ a := by
  have he : ∀ k x, M.eta α k x = α + M.γ k := fun k x => by
    simp [eta, metaRegressionPredictor, hβ₁, hβ₂]
  have hm : ∀ k, M.armMean ginv α F k = ginv (α + M.γ k) := fun k => by
    simp [armMean, surface, he]
  refine ⟨he, hm, fun a b => ?_⟩
  change g (M.armMean ginv α F b) - g (M.armMean ginv α F a) = _
  rw [hm, hm, hg, hg]
  ring

end MultilevelModel

end NetworkMetaRegression

end CausalInference
