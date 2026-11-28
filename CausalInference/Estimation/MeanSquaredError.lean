/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.Estimation.BernoulliPair
public import CausalInference.BiasAnalysis.MeasurementError

/-!
# The bias and variance decomposition of the mean squared error

For an estimator `T` of a target `g` with finite second moment,
`E[(T - g)²] = Var(T) + (E[T] - g)²`: the mean squared error is the variance plus the squared
bias. For a vector estimator `T = (T_i)_i` of `g = (g_i)_i`, the mean squared error matrix
`E[(T - g)(T - g)ᵀ]` is the covariance matrix plus the outer product of the bias vector, and its
trace (the total mean squared error) is the sum of the variances plus the squared Euclidean norm
of the bias.

## Main definitions

* `CausalInference.mseMatrix μ T g`: the mean squared error matrix `E[(T - g)(T - g)ᵀ]`.
* `CausalInference.biasVec μ T g`: the bias vector `E[T] - g`.

## Main results

* `CausalInference.integral_sub_mul_sub`: `E[(X - a)(Y - c)] = cov(X, Y) + (E X - a)(E Y - c)`.
* `CausalInference.integral_sub_sq`: **mean squared error = variance + squared bias**.
* `CausalInference.mseMatrix_eq`: `E[(T - g)(T - g)ᵀ] = Cov(T) + b bᵀ`.
* `CausalInference.trace_mseMatrix`: the total mean squared error.
* Instances: the shrunken Bernoulli estimator `X / 2` of `p` (`bernoulli_variance_half`) and
  the coordinate indicators of a pair of independent Bernoulli variables
  (`bernoulliPair_covMatrix_indicators`).

References: E. L. Lehmann and G. Casella (1998), *Theory of Point Estimation*, second edition,
chapter 2.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Matrix

namespace CausalInference

open BiasAnalysis.MeasurementError (covMatrix)

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- `E[(X - a)(Y - c)] = cov(X, Y) + (E X - a)(E Y - c)` for square integrable `X, Y`. -/
theorem integral_sub_mul_sub {X Y : Ω → ℝ} (hX : MemLp X 2 μ) (hY : MemLp Y 2 μ) (a c : ℝ) :
    ∫ ω, (X ω - a) * (Y ω - c) ∂μ = cov[X, Y; μ] + (μ[X] - a) * (μ[Y] - c) := by
  have hX' : MemLp (fun ω ↦ X ω - a) 2 μ := hX.sub (memLp_const a)
  have hY' : MemLp (fun ω ↦ Y ω - c) 2 μ := hY.sub (memLp_const c)
  have h := covariance_eq_sub hX' hY'
  rw [covariance_sub_const_left (hX.integrable one_le_two),
    covariance_sub_const_right (hY.integrable one_le_two),
    integral_sub (hX.integrable one_le_two) (integrable_const a),
    integral_sub (hY.integrable one_le_two) (integrable_const c)] at h
  simp only [integral_const, probReal_univ, smul_eq_mul, one_mul] at h
  change cov[X, Y; μ] = ∫ ω, (X ω - a) * (Y ω - c) ∂μ - (μ[X] - a) * (μ[Y] - c) at h
  linarith

/-- **Mean squared error = variance + squared bias.** For a square integrable estimator `T` of
`g`, `E[(T - g)²] = Var(T) + (E[T] - g)²`. -/
theorem integral_sub_sq {T : Ω → ℝ} (hT : MemLp T 2 μ) (g : ℝ) :
    ∫ ω, (T ω - g) ^ 2 ∂μ = Var[T; μ] + (μ[T] - g) ^ 2 := by
  simp only [sq]
  rw [integral_sub_mul_sub hT hT g g, covariance_self hT.aemeasurable]

variable {ι : Type*} [Fintype ι]

/-- The mean squared error matrix `E[(T - g)(T - g)ᵀ]` of a vector estimator `T` of `g`. -/
noncomputable def mseMatrix (μ : Measure Ω) (T : ι → Ω → ℝ) (g : ι → ℝ) : Matrix ι ι ℝ :=
  Matrix.of fun i j ↦ ∫ ω, (T i ω - g i) * (T j ω - g j) ∂μ

/-- The bias vector `E[T] - g` of a vector estimator `T` of `g`. -/
noncomputable def biasVec (μ : Measure Ω) (T : ι → Ω → ℝ) (g : ι → ℝ) : ι → ℝ :=
  fun i ↦ μ[T i] - g i

omit [Fintype ι] in
/-- **The matrix form**: the mean squared error matrix of a square integrable vector estimator is
the covariance matrix plus the outer product of the bias vector,
`E[(T - g)(T - g)ᵀ] = Cov(T) + b bᵀ`. -/
theorem mseMatrix_eq {T : ι → Ω → ℝ} (hT : ∀ i, MemLp (T i) 2 μ) (g : ι → ℝ) :
    mseMatrix μ T g = covMatrix μ T + vecMulVec (biasVec μ T g) (biasVec μ T g) := by
  ext i j
  rw [mseMatrix, of_apply, integral_sub_mul_sub (hT i) (hT j), Matrix.add_apply,
    vecMulVec_apply]
  rfl

/-- **The total mean squared error** `E‖T - g‖² = tr E[(T - g)(T - g)ᵀ]` is the sum of the
variances plus the squared norm of the bias. -/
theorem trace_mseMatrix {T : ι → Ω → ℝ} (hT : ∀ i, MemLp (T i) 2 μ) (g : ι → ℝ) :
    (mseMatrix μ T g).trace = ∑ i, Var[T i; μ] + ∑ i, (μ[T i] - g i) ^ 2 := by
  rw [mseMatrix_eq hT, trace_add, trace, trace]
  simp only [diag_apply, vecMulVec_apply, biasVec, sq]
  congr 1
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  exact covariance_self (hT i).aemeasurable

/-! ### Instances -/

open ParametricFamily

/-- **The shrunken Bernoulli estimator.** For `X ~ Bernoulli(p)`, the estimator `T = X / 2` of
`p` has mean squared error `p / 4`, bias `-p / 2`, and so, by `integral_sub_sq`, variance
`p (1 - p) / 4`. -/
theorem bernoulli_variance_half {p : ℝ} (hp : p ∈ Set.Ioo (0 : ℝ) 1) :
    ∫ x, ((if x then 1 else 0 : ℝ) / 2 - p) ^ 2 ∂bernoulli.law p = p / 4 ∧
      Var[fun x : Bool ↦ (if x then 1 else 0 : ℝ) / 2; bernoulli.law p] = p * (1 - p) / 4 := by
  have := isProbabilityMeasure_law (F := bernoulli) hp
  have hmse := integral_sub_sq (μ := bernoulli.law p)
    (T := fun x : Bool ↦ (if x then 1 else 0 : ℝ) / 2) .of_discrete p
  have h1 : ∫ x, ((if x then 1 else 0 : ℝ) / 2 - p) ^ 2 ∂bernoulli.law p = p / 4 := by
    rw [bernoulli_integral_law hp]
    simp only [ite_true, Bool.false_eq_true, ite_false]
    ring
  have h2 : ∫ x, (if x then 1 else 0 : ℝ) / 2 ∂bernoulli.law p = p / 2 := by
    rw [bernoulli_integral_law hp]
    simp only [ite_true, Bool.false_eq_true, ite_false]
    ring
  refine ⟨h1, ?_⟩
  rw [h1, h2] at hmse
  linarith

/-- The success indicators of the two coordinates of a pair. -/
noncomputable def pairIndicators : Fin 2 → Bool × Bool → ℝ :=
  ![fun x ↦ if x.1 then 1 else 0, fun x ↦ if x.2 then 1 else 0]

/-- **A matrix instance.** Under the law of a pair of independent Bernoulli variables with
success probabilities `θ`, the coordinate indicators are unbiased for `θ`, their mean squared
error matrix is `diag(θ₀ (1 - θ₀), θ₁ (1 - θ₁))`, and so, by `mseMatrix_eq`, this is also their
covariance matrix. -/
theorem bernoulliPair_covMatrix_indicators {θ : Fin 2 → ℝ} (hθ : θ ∈ bernoulliPair.Θ) :
    biasVec (bernoulliPair.law θ) pairIndicators θ = 0 ∧
      covMatrix (bernoulliPair.law θ) pairIndicators =
        diagonal ![θ 0 * (1 - θ 0), θ 1 * (1 - θ 1)] := by
  have := isProbabilityMeasure_law hθ
  have hb : biasVec (bernoulliPair.law θ) pairIndicators θ = 0 := by
    funext i
    simp only [biasVec, Pi.zero_apply]
    rw [bernoulliPair_integral_law hθ]
    fin_cases i <;> simp [pairIndicators] <;> ring
  have hm := mseMatrix_eq (μ := bernoulliPair.law θ) (T := pairIndicators)
    (fun _ ↦ .of_discrete) θ
  rw [hb, vecMulVec_zero, add_zero] at hm
  refine ⟨hb, ?_⟩
  rw [← hm]
  ext i j
  rw [mseMatrix, of_apply, bernoulliPair_integral_law hθ]
  fin_cases i <;> fin_cases j <;> simp [pairIndicators] <;> ring

end CausalInference
