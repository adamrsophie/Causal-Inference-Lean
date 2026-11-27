/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.BiasAnalysis.VarianceFormulas
public import CausalInference.BiasAnalysis.MeasurementError
public import CausalInference.Estimation.DeltaMethodMultivariate

/-!
# Covariance-aware first-order variances and the printed variance formulas as asymptotic variances

The variance formulas of Chapter 10 of Fox, MacLehose and Lash (`VarianceFormulas`) are sums of
squared partial derivatives times input variances, `firstOrderVariance`. This file supplies the
covariance-aware form and connects three of the printed formulas to the multivariate delta method
(`IsAsymptoticallyLinear.comp_hasFDerivAt`).

Main definitions and results:

* `quadraticVariance grad C = ∑ i, ∑ j, gradᵢ gradⱼ C i j`: the first-order variance of a smooth
  function of correlated inputs with covariance matrix `C`.
* `variance_linearization_cov`: the variance of a linear combination `∑ i, gᵢ Xᵢ` of square
  integrable variables is `quadraticVariance g (covMatrix μ X)`, with all covariances.
* `quadraticVariance_of_offDiag_eq_zero`, `variance_linearization_of_uncorrelated`,
  `variance_linearization_of_indep`: when the inputs are uncorrelated the quadratic form is
  `firstOrderVariance`, which recovers `VarianceFormulas.variance_linearization`.
* `firstOrderVariance_div`: the first-order variance scales with the input variances.
* `asymptoticVariance_eq_quadraticVariance`, `asymptoticVariance_eq_firstOrderVariance`: for
  asymptotically linear inputs and a function differentiable at the limit, the delta method
  estimator is asymptotically linear and its asymptotic variance is the quadratic form of the
  partial derivatives in the covariance matrix of the influence functions; it is
  `firstOrderVariance` of the partial derivatives and the input asymptotic variances when the
  influence functions are pairwise independent.
* `greenland_nondifferential_asymptotic`, `marshall_asymptotic`, `ivPooled_asymptotic`: the
  printed Greenland (nondifferential), Marshall and inverse-variance pooled variances are the
  asymptotic variances given by the multivariate delta method.

## Sampling assumptions

All inputs are computed from one i.i.d. sample `O` with one sample size `n` (the model of
`IsAsymptoticallyLinear`). Independent studies (a validation study and a main study, or cases and
controls) enter as independent components of one observation, and the assumption used is
pairwise independence of the influence functions at the first observation. The input asymptotic
variances are hypotheses: for example `pe (1 - pe) / D` for an observed proportion. In the printed
formulas `D` is the size of the group; the asymptotic variance here is per observation, so the
printed variance is the asymptotic variance divided by `n` when every input comes from the same
`n` observations, which is the case `D = 1` here. Inputs from studies of different sizes with a
fixed ratio need the two-sample extension described in `DeltaMethodMultivariate`, which is not
formalized.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Finset

namespace CausalInference

namespace BiasAnalysis.VarianceCovariance

open VarianceFormulas MeasurementError

/-! ### Quadratic forms and variances of linear combinations -/

/-- The first-order variance `∑ i, ∑ j, gradᵢ gradⱼ C i j` of a smooth function of inputs with
covariance matrix `C`, where `gradᵢ` is the partial derivative in the `i`th input. -/
def quadraticVariance {ι : Type*} [Fintype ι] (grad : ι → ℝ) (C : Matrix ι ι ℝ) : ℝ :=
  ∑ i, ∑ j, grad i * grad j * C i j

/-- The quadratic form is the dot product of `grad` with `C` applied to `grad`. -/
theorem quadraticVariance_eq_dotProduct {ι : Type*} [Fintype ι] (grad : ι → ℝ)
    (C : Matrix ι ι ℝ) : quadraticVariance grad C = dotProduct grad (C.mulVec grad) := by
  simp only [quadraticVariance, dotProduct, Matrix.mulVec, mul_sum]
  refine sum_congr rfl fun i _ ↦ sum_congr rfl fun j _ ↦ ?_
  ring

/-- **Uncorrelated inputs.** If the off-diagonal entries of `C` vanish, the quadratic form is the
sum of squared partial derivatives times the diagonal entries, `firstOrderVariance`. -/
theorem quadraticVariance_of_offDiag_eq_zero {k : ℕ} (grad : Fin k → ℝ)
    {C : Matrix (Fin k) (Fin k) ℝ} (hC : ∀ i j, i ≠ j → C i j = 0) :
    quadraticVariance grad C = firstOrderVariance grad fun i ↦ C i i := by
  simp only [quadraticVariance, firstOrderVariance]
  refine sum_congr rfl fun i _ ↦ ?_
  rw [sum_eq_single i]
  · ring
  · intro j _ hji
    rw [hC i j hji.symm, mul_zero]
  · intro hi
    exact absurd (mem_univ i) hi

/-- **Per observation and per study scale.** Dividing every input variance by `n` divides the
first-order variance by `n`: an asymptotic variance per observation, divided by the sample size,
is the variance printed for a sample of size `n`. -/
theorem firstOrderVariance_div {k : ℕ} (grad var : Fin k → ℝ) (n : ℝ) :
    firstOrderVariance grad (fun i ↦ var i / n) = firstOrderVariance grad var / n := by
  simp only [firstOrderVariance, sum_div, mul_div_assoc]

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}

/-- **Variance of a linear combination, with covariances.** For square integrable `Xᵢ` under a
finite measure, `Var(∑ i, gᵢ Xᵢ) = ∑ i, ∑ j, gᵢ gⱼ Cov(Xᵢ, Xⱼ)`. This is the step of the
multivariate delta method that turns a gradient and a covariance matrix into a variance. -/
theorem variance_linearization_cov [IsFiniteMeasure μ] {ι : Type*} [Fintype ι]
    (X : ι → Ω → ℝ) (hX : ∀ i, MemLp (X i) 2 μ) (g : ι → ℝ) :
    Var[fun ω ↦ ∑ i, g i * X i ω; μ] = quadraticVariance g (covMatrix μ X) := by
  rw [variance_fun_sum (X := fun i ω ↦ g i * X i ω) fun i ↦ (hX i).const_mul (g i)]
  simp only [quadraticVariance, covMatrix, Matrix.of_apply]
  refine sum_congr rfl fun i _ ↦ sum_congr rfl fun j _ ↦ ?_
  rw [covariance_const_mul_left, covariance_const_mul_right]
  ring

/-- The diagonal of the covariance matrix holds the variances. -/
theorem covMatrix_apply_self {ι : Type*} (X : ι → Ω → ℝ) (i : ι) (hX : AEMeasurable (X i) μ) :
    covMatrix μ X i i = Var[X i; μ] := by
  simp only [covMatrix, Matrix.of_apply]
  exact covariance_self hX

/-- **Uncorrelated inputs.** If `Cov(Xᵢ, Xⱼ) = 0` for `i ≠ j`, the variance of `∑ i, gᵢ Xᵢ` is
`firstOrderVariance g (Var Xᵢ)`. -/
theorem variance_linearization_of_uncorrelated [IsFiniteMeasure μ] {k : ℕ} (X : Fin k → Ω → ℝ)
    (hX : ∀ i, MemLp (X i) 2 μ) (hunc : ∀ i j, i ≠ j → cov[X i, X j; μ] = 0) (g : Fin k → ℝ) :
    Var[fun ω ↦ ∑ i, g i * X i ω; μ] = firstOrderVariance g fun i ↦ Var[X i; μ] := by
  rw [variance_linearization_cov X hX g,
    quadraticVariance_of_offDiag_eq_zero g fun i j hij ↦ by
      simp only [covMatrix, Matrix.of_apply]
      exact hunc i j hij]
  simp only [covMatrix_apply_self X _ (hX _).aemeasurable]

/-- **Independent inputs.** Pairwise independent inputs are uncorrelated, so the covariance form
recovers `VarianceFormulas.variance_linearization`. -/
theorem variance_linearization_of_indep [IsProbabilityMeasure μ] {k : ℕ} (X : Fin k → Ω → ℝ)
    (hX : ∀ i, MemLp (X i) 2 μ) (hind : Pairwise fun i j ↦ IndepFun (X i) (X j) μ)
    (g : Fin k → ℝ) :
    Var[fun ω ↦ ∑ i, g i * X i ω; μ] = firstOrderVariance g fun i ↦ Var[X i; μ] :=
  variance_linearization_of_uncorrelated X hX
    (fun i j hij ↦ (hind hij).covariance_eq_zero (hX i) (hX j)) g

/-- The two forms agree: under the hypotheses of `variance_linearization`, the covariance form
gives the same value. -/
theorem variance_linearization_eq_of_indep [IsProbabilityMeasure μ] {k : ℕ} (X : Fin k → Ω → ℝ)
    (hX : ∀ i, MemLp (X i) 2 μ) (hind : Pairwise fun i j ↦ IndepFun (X i) (X j) μ)
    (g : Fin k → ℝ) :
    quadraticVariance g (covMatrix μ X) = firstOrderVariance g fun i ↦ Var[X i; μ] := by
  rw [← variance_linearization_cov X hX g, variance_linearization X hX hind g]

/-! ### The asymptotic variance from the multivariate delta method -/

variable {𝒪 : Type*} [MeasurableSpace 𝒪] {O : ℕ → Ω → 𝒪}

/-- **Asymptotic variance, correlated inputs.** If `θhat i` is asymptotically linear at `θ i`
with influence function `φ i`, `g` is differentiable at `θ`, and `dᵢ` is the derivative of `g`
along the `i`th coordinate line through `θ`, then `g (θhat · n)` is asymptotically linear at
`g θ` with influence function `∑ i, dᵢ φ i`, and its asymptotic variance is
`quadraticVariance d` of the covariance matrix of the influence functions. -/
theorem asymptoticVariance_eq_quadraticVariance [IsProbabilityMeasure μ] {ι : Type*} [Fintype ι]
    [DecidableEq ι] (hO : IsIIDSample O μ) {θhat : ι → ℕ → Ω → ℝ} {θ : ι → ℝ}
    {φ : ι → 𝒪 → ℝ} (h : ∀ i, IsAsymptoticallyLinear (θhat i) (θ i) (φ i) O μ)
    {g : (ι → ℝ) → ℝ} (hg : DifferentiableAt ℝ g θ) {d : ι → ℝ}
    (hd : ∀ i, HasDerivAt (fun t ↦ g (Function.update θ i t)) (d i) (θ i)) :
    IsAsymptoticallyLinear (fun n ω ↦ g (fun i ↦ θhat i n ω)) (g θ)
        (fun x ↦ ∑ i, d i * φ i x) O μ ∧
      μ[fun ω ↦ (∑ i, d i * φ i (O 0 ω)) ^ 2] =
        quadraticVariance d (covMatrix μ fun i ω ↦ φ i (O 0 ω)) := by
  refine ⟨IsAsymptoticallyLinear.comp_of_partials hO h hg hd, ?_⟩
  rw [IsAsymptoticallyLinear.integral_sq_eq_sum_cov h d]
  simp only [quadraticVariance, covMatrix, Matrix.of_apply]

/-- **Asymptotic variance, independent inputs.** Under the hypotheses of
`asymptoticVariance_eq_quadraticVariance`, if the influence functions are pairwise independent at
the observation and have second moments `σ2ᵢ` (the asymptotic variances of the inputs), the
asymptotic variance of `g (θhat · n)` is `firstOrderVariance d σ2`. -/
theorem asymptoticVariance_eq_firstOrderVariance [IsProbabilityMeasure μ] {k : ℕ}
    (hO : IsIIDSample O μ) {θhat : Fin k → ℕ → Ω → ℝ} {θ : Fin k → ℝ} {φ : Fin k → 𝒪 → ℝ}
    (h : ∀ i, IsAsymptoticallyLinear (θhat i) (θ i) (φ i) O μ)
    (hind : Pairwise fun i j ↦ IndepFun (fun ω ↦ φ i (O 0 ω)) (fun ω ↦ φ j (O 0 ω)) μ)
    {σ2 : Fin k → ℝ} (hσ : ∀ i, μ[fun ω ↦ φ i (O 0 ω) ^ 2] = σ2 i)
    {g : (Fin k → ℝ) → ℝ} (hg : DifferentiableAt ℝ g θ) {d : Fin k → ℝ}
    (hd : ∀ i, HasDerivAt (fun t ↦ g (Function.update θ i t)) (d i) (θ i)) :
    IsAsymptoticallyLinear (fun n ω ↦ g (fun i ↦ θhat i n ω)) (g θ)
        (fun x ↦ ∑ i, d i * φ i x) O μ ∧
      μ[fun ω ↦ (∑ i, d i * φ i (O 0 ω)) ^ 2] = firstOrderVariance d σ2 := by
  refine ⟨IsAsymptoticallyLinear.comp_of_partials hO h hg hd, ?_⟩
  rw [IsAsymptoticallyLinear.integral_sq_of_indep h hind d]
  simp only [firstOrderVariance, hσ]

/-! ### Greenland variance, nondifferential misclassification -/

/-- The nondifferential bias-adjusted log odds ratio as a function of the input vector
`(SE, SP, pe₁, pe₀)`. -/
noncomputable def logORSeSpNondiffVec (v : Fin 4 → ℝ) : ℝ :=
  logORSeSp (v 0) (v 1) (v 2) (v 0) (v 1) (v 3)

/-- The nondifferential adjusted log odds ratio is differentiable at an admissible point. -/
theorem differentiableAt_logORSeSpNondiffVec {se sp pe₁ pe₀ : ℝ} (hA₁ : 0 < pe₁ + sp - 1)
    (hB₁ : 0 < se - pe₁) (hA₀ : 0 < pe₀ + sp - 1) (hB₀ : 0 < se - pe₀) :
    DifferentiableAt ℝ logORSeSpNondiffVec ![se, sp, pe₁, pe₀] := by
  have p : ∀ i : Fin 4, DifferentiableAt ℝ (fun v : Fin 4 → ℝ ↦ v i) ![se, sp, pe₁, pe₀] :=
    fun i ↦ differentiableAt_apply i _
  unfold logORSeSpNondiffVec logORSeSp logOddsSeSp
  refine (((((p 2).add (p 1)).sub_const 1).log ?_).sub (((p 0).sub (p 2)).log ?_)).sub
    (((((p 3).add (p 1)).sub_const 1).log ?_).sub (((p 0).sub (p 3)).log ?_))
  · exact hA₁.ne'
  · exact hB₁.ne'
  · exact hA₀.ne'
  · exact hB₀.ne'

/-- **The Greenland nondifferential variance is an asymptotic variance.** Let `θhat 0`, `θhat 1`,
`θhat 2`, `θhat 3` estimate `SE`, `SP` and the observed exposure proportions `pe₁` (cases) and
`pe₀` (controls), asymptotically linear with pairwise independent influence functions of
asymptotic variances `Var SE`, `Var SP`, `pe₁ (1 - pe₁) / D₁` and `pe₀ (1 - pe₀) / D₀`. At an
admissible point, the plug-in adjusted log odds ratio is asymptotically linear at the true
adjusted log odds ratio, with influence function the gradient of `greenland_nondifferential`
applied to the influence functions, and its asymptotic variance is `greenlandNondiff`. -/
theorem greenland_nondifferential_asymptotic [IsProbabilityMeasure μ] (hO : IsIIDSample O μ)
    {θhat : Fin 4 → ℕ → Ω → ℝ} {φ : Fin 4 → 𝒪 → ℝ} {vse vsp se sp pe₁ D₁ pe₀ D₀ : ℝ}
    (h : ∀ i, IsAsymptoticallyLinear (θhat i) (![se, sp, pe₁, pe₀] i) (φ i) O μ)
    (hind : Pairwise fun i j ↦ IndepFun (fun ω ↦ φ i (O 0 ω)) (fun ω ↦ φ j (O 0 ω)) μ)
    (hσ : ∀ i, μ[fun ω ↦ φ i (O 0 ω) ^ 2] =
      ![vse, vsp, pe₁ * (1 - pe₁) / D₁, pe₀ * (1 - pe₀) / D₀] i)
    (hA₁ : 0 < pe₁ + sp - 1) (hB₁ : 0 < se - pe₁) (hD₁ : 0 < D₁)
    (hA₀ : 0 < pe₀ + sp - 1) (hB₀ : 0 < se - pe₀) (hD₀ : 0 < D₀) :
    IsAsymptoticallyLinear
        (fun n ω ↦ logORSeSp (θhat 0 n ω) (θhat 1 n ω) (θhat 2 n ω) (θhat 0 n ω) (θhat 1 n ω)
          (θhat 3 n ω))
        (logORSeSp se sp pe₁ se sp pe₀)
        (fun x ↦ ∑ i, ![-(1 / (se - pe₁)) + 1 / (se - pe₀), 1 / (pe₁ + sp - 1) - 1 / (pe₀ + sp - 1),
          1 / (pe₁ + sp - 1) + 1 / (se - pe₁), -(1 / (pe₀ + sp - 1) + 1 / (se - pe₀))] i *
            φ i x) O μ ∧
      μ[fun ω ↦ (∑ i, ![-(1 / (se - pe₁)) + 1 / (se - pe₀),
          1 / (pe₁ + sp - 1) - 1 / (pe₀ + sp - 1), 1 / (pe₁ + sp - 1) + 1 / (se - pe₁),
          -(1 / (pe₀ + sp - 1) + 1 / (se - pe₀))] i * φ i (O 0 ω)) ^ 2] =
        greenlandNondiff vse vsp se sp pe₁ D₁ pe₀ D₀ := by
  obtain ⟨d0, d1, d2, d3, hvar⟩ := greenland_nondifferential (vse := vse) (vsp := vsp)
    hA₁ hB₁ hD₁ hA₀ hB₀ hD₀
  have hd : ∀ i, HasDerivAt (fun t ↦ logORSeSpNondiffVec (Function.update ![se, sp, pe₁, pe₀] i t))
      (![-(1 / (se - pe₁)) + 1 / (se - pe₀), 1 / (pe₁ + sp - 1) - 1 / (pe₀ + sp - 1),
          1 / (pe₁ + sp - 1) + 1 / (se - pe₁), -(1 / (pe₀ + sp - 1) + 1 / (se - pe₀))] i)
      (![se, sp, pe₁, pe₀] i) := by
    intro i
    fin_cases i
    · refine d0.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t ↦ ?_)
      simp [logORSeSpNondiffVec]
    · refine d1.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t ↦ ?_)
      simp [logORSeSpNondiffVec]
    · refine d2.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t ↦ ?_)
      simp [logORSeSpNondiffVec]
    · refine d3.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t ↦ ?_)
      simp [logORSeSpNondiffVec]
  have key := asymptoticVariance_eq_firstOrderVariance hO h hind hσ
    (differentiableAt_logORSeSpNondiffVec hA₁ hB₁ hA₀ hB₀) hd
  rw [hvar] at key
  exact key

/-! ### Marshall variance -/

/-- The predictive-value adjusted log odds ratio as a function of the input vector
`(PPV₁, NPV₁, pe₁, PPV₀, NPV₀, pe₀)`. -/
noncomputable def logORPVVec (v : Fin 6 → ℝ) : ℝ :=
  logORPV (v 0) (v 1) (v 2) (v 3) (v 4) (v 5)

/-- The log odds of the predictive-value corrected proportion, as a function of a vector, is
differentiable where the corrected proportion lies strictly inside `(0, 1)`. -/
theorem differentiableAt_logOddsPV_comp {v : Fin 6 → ℝ} (a b c : Fin 6)
    (hP₀ : 0 < trueProportionPV (v a) (v b) (v c)) (hP₁ : trueProportionPV (v a) (v b) (v c) < 1) :
    DifferentiableAt ℝ (fun w : Fin 6 → ℝ ↦ logOddsPV (w a) (w b) (w c)) v := by
  have hl := (hasDerivAt_logit hP₀ hP₁).differentiableAt
  have hT : DifferentiableAt ℝ (fun w : Fin 6 → ℝ ↦ trueProportionPV (w a) (w b) (w c)) v := by
    unfold trueProportionPV
    have pa := differentiableAt_apply (𝕜 := ℝ) a v
    have pb := differentiableAt_apply (𝕜 := ℝ) b v
    have pc := differentiableAt_apply (𝕜 := ℝ) c v
    exact (pa.mul pc).add ((pb.const_sub 1).mul (pc.const_sub 1))
  exact hl.comp v hT

/-- **The Marshall variance is an asymptotic variance.** Let `θhat` estimate
`(PPV₁, NPV₁, pe₁, PPV₀, NPV₀, pe₀)`, asymptotically linear with pairwise independent influence
functions of asymptotic variances `(Var PPV₁, Var NPV₁, Var pe₁, Var PPV₀, Var NPV₀, Var pe₀)`.
Where both corrected proportions lie strictly inside `(0, 1)`, the plug-in adjusted log odds
ratio `logORPV` is asymptotically linear at the true adjusted log odds ratio with the influence
function given by the gradient of `hasDerivAt_logORPV`, and its asymptotic variance is the
Marshall variance `a₀ / (P(E₀)(1 - P(E₀)))² + a₁ / (P(E₁)(1 - P(E₁)))²` of `marshall_variance`. -/
theorem marshall_asymptotic [IsProbabilityMeasure μ] (hO : IsIIDSample O μ)
    {θhat : Fin 6 → ℕ → Ω → ℝ} {φ : Fin 6 → 𝒪 → ℝ}
    {vppv₁ vnpv₁ vpe₁ ppv₁ npv₁ pe₁ vppv₀ vnpv₀ vpe₀ ppv₀ npv₀ pe₀ : ℝ}
    (h : ∀ i, IsAsymptoticallyLinear (θhat i) (![ppv₁, npv₁, pe₁, ppv₀, npv₀, pe₀] i) (φ i) O μ)
    (hind : Pairwise fun i j ↦ IndepFun (fun ω ↦ φ i (O 0 ω)) (fun ω ↦ φ j (O 0 ω)) μ)
    (hσ : ∀ i, μ[fun ω ↦ φ i (O 0 ω) ^ 2] = ![vppv₁, vnpv₁, vpe₁, vppv₀, vnpv₀, vpe₀] i)
    (hP₁₀ : 0 < trueProportionPV ppv₁ npv₁ pe₁) (hP₁₁ : trueProportionPV ppv₁ npv₁ pe₁ < 1)
    (hP₀₀ : 0 < trueProportionPV ppv₀ npv₀ pe₀) (hP₀₁ : trueProportionPV ppv₀ npv₀ pe₀ < 1) :
    let P₁ := trueProportionPV ppv₁ npv₁ pe₁
    let P₀ := trueProportionPV ppv₀ npv₀ pe₀
    let grad : Fin 6 → ℝ :=
      ![pe₁ / (P₁ * (1 - P₁)), -(1 - pe₁) / (P₁ * (1 - P₁)), (ppv₁ - (1 - npv₁)) / (P₁ * (1 - P₁)),
        -(pe₀ / (P₀ * (1 - P₀))), -(-(1 - pe₀) / (P₀ * (1 - P₀))),
        -((ppv₀ - (1 - npv₀)) / (P₀ * (1 - P₀)))]
    IsAsymptoticallyLinear
        (fun n ω ↦ logORPV (θhat 0 n ω) (θhat 1 n ω) (θhat 2 n ω) (θhat 3 n ω) (θhat 4 n ω)
          (θhat 5 n ω))
        (logORPV ppv₁ npv₁ pe₁ ppv₀ npv₀ pe₀) (fun x ↦ ∑ i, grad i * φ i x) O μ ∧
      μ[fun ω ↦ (∑ i, grad i * φ i (O 0 ω)) ^ 2] =
        marshallA vppv₀ vnpv₀ vpe₀ ppv₀ npv₀ pe₀ / (P₀ * (1 - P₀)) ^ 2 +
          marshallA vppv₁ vnpv₁ vpe₁ ppv₁ npv₁ pe₁ / (P₁ * (1 - P₁)) ^ 2 := by
  intro P₁ P₀ grad
  obtain ⟨d0, d1, d2, d3, d4, d5⟩ := hasDerivAt_logORPV hP₁₀ hP₁₁ hP₀₀ hP₀₁
  set θ : Fin 6 → ℝ := ![ppv₁, npv₁, pe₁, ppv₀, npv₀, pe₀] with hθ
  have hg : DifferentiableAt ℝ logORPVVec θ := by
    unfold logORPVVec logORPV
    exact (differentiableAt_logOddsPV_comp (v := θ) 0 1 2 hP₁₀ hP₁₁).sub
      (differentiableAt_logOddsPV_comp (v := θ) 3 4 5 hP₀₀ hP₀₁)
  have hd : ∀ i, HasDerivAt (fun t ↦ logORPVVec (Function.update θ i t)) (grad i) (θ i) := by
    intro i
    fin_cases i
    · refine d0.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t ↦ ?_)
      simp [hθ, logORPVVec]
    · refine d1.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t ↦ ?_)
      simp [hθ, logORPVVec]
    · refine d2.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t ↦ ?_)
      simp [hθ, logORPVVec]
    · refine d3.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t ↦ ?_)
      simp [hθ, logORPVVec]
    · refine d4.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t ↦ ?_)
      simp [hθ, logORPVVec]
    · refine d5.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t ↦ ?_)
      simp [hθ, logORPVVec]
  have key := asymptoticVariance_eq_firstOrderVariance hO h hind hσ hg hd
  rw [marshall_variance hP₁₀ hP₁₁ hP₀₀ hP₀₁] at key
  exact key

/-! ### Inverse-variance pooling -/

/-- **The inverse-variance pooled variance is an asymptotic variance.** Let `θhat i`
(`i < k`, `k > 0`) be asymptotically linear at `θ i` with pairwise independent influence
functions of asymptotic variances `Vᵢ > 0`, and pool them with the inverse-variance weights of
the known `Vᵢ`. Then the pooled estimate is asymptotically linear at `ivPooled θ V` with
influence function `∑ i, ((1 / Vᵢ) / ∑ⱼ (1 / Vⱼ)) φ i`, and its asymptotic variance is
`ivPooledVariance V = 1 / ∑ⱼ (1 / Vⱼ)`. The weights are fixed constants here; estimated weights
are not covered. -/
theorem ivPooled_asymptotic [IsProbabilityMeasure μ] {k : ℕ} (hk : 0 < k)
    (hO : IsIIDSample O μ) {θhat : Fin k → ℕ → Ω → ℝ} {θ : Fin k → ℝ} {φ : Fin k → 𝒪 → ℝ}
    (h : ∀ i, IsAsymptoticallyLinear (θhat i) (θ i) (φ i) O μ)
    (hind : Pairwise fun i j ↦ IndepFun (fun ω ↦ φ i (O 0 ω)) (fun ω ↦ φ j (O 0 ω)) μ)
    {V : Fin k → ℝ} (hV : ∀ i, 0 < V i) (hσ : ∀ i, μ[fun ω ↦ φ i (O 0 ω) ^ 2] = V i) :
    IsAsymptoticallyLinear (fun n ω ↦ ivPooled (fun i ↦ θhat i n ω) V) (ivPooled θ V)
        (fun x ↦ ∑ i, (1 / V i) / ivTotalWeight V * φ i x) O μ ∧
      μ[fun ω ↦ (∑ i, (1 / V i) / ivTotalWeight V * φ i (O 0 ω)) ^ 2] = ivPooledVariance V := by
  set w : Fin k → ℝ := fun i ↦ (1 / V i) / ivTotalWeight V with hw
  let L : (Fin k → ℝ) →L[ℝ] ℝ := ∑ i, w i • ContinuousLinearMap.proj i
  have hL : (fun v ↦ ivPooled v V) = ⇑L := by
    funext v
    simp only [ivPooled, L, FunLike.coe_sum, Finset.sum_apply, FunLike.coe_smul, Pi.smul_apply,
      smul_eq_mul, hw, Finset.sum_div]
    refine sum_congr rfl fun i _ ↦ ?_
    rw [ContinuousLinearMap.proj_apply]
    ring
  have hLs : ∀ i, L (Pi.single i 1) = w i := by
    intro i
    simp [L, Pi.single_apply]
  have hAL := IsAsymptoticallyLinear.comp_hasFDerivAt hO h (g := fun v ↦ ivPooled v V)
    (L := L) (by rw [hL]; exact L.hasFDerivAt)
  simp only [hLs] at hAL
  refine ⟨hAL, ?_⟩
  rw [IsAsymptoticallyLinear.integral_sq_of_indep h hind w]
  have := (firstOrderVariance_ivWeights hV hk).2
  simp only [firstOrderVariance] at this
  simp only [hσ]
  exact this

end BiasAnalysis.VarianceCovariance

end CausalInference
