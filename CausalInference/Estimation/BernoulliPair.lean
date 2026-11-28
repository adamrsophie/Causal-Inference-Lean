/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.Estimation.CramerRaoVector
public import CausalInference.Estimation.BernoulliFamily

/-!
# Two independent Bernoulli observations: a two-parameter family

The family of a pair `(X₁, X₂)` of independent Bernoulli variables with success probabilities
`θ₀, θ₁ ∈ (0, 1)`: sample space `Bool × Bool` with counting measure, parameter `θ : Fin 2 → ℝ`
and density `f(x;θ) = f(x₁;θ₀) f(x₂;θ₁)`. Every hypothesis of the vector theorems is discharged:
the family is regular at every parameter, its information matrix is
`diag(1 / (θ₀ (1 - θ₀)), 1 / (θ₁ (1 - θ₁)))`, which is positive definite, and the pair of success
indicators is an unbiased estimator whose covariance matrix equals `I(θ)⁻¹`, so it attains the
matrix Cramér-Rao bound.

## Main results

* `CausalInference.ParametricFamily.bernoulliPair_isRegularAtVec`: regularity.
* `CausalInference.ParametricFamily.bernoulliPair_fisherInfoMatrix`: the information matrix.
* `CausalInference.ParametricFamily.bernoulliPair_cramer_rao_matrix_attained`: the matrix bound
  holds for the pair of success indicators and is attained.
* `CausalInference.ParametricFamily.bernoulliPair_cramer_rao_gradient`: the gradient bound for
  the first success indicator.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology Metric Matrix
open CausalInference.BiasAnalysis.MeasurementError (covMatrix)
open scoped ENNReal

namespace CausalInference

namespace ParametricFamily

/-- Two independent Bernoulli observations with success probabilities `θ 0` and `θ 1`. -/
noncomputable def bernoulliPair : ParametricFamily (Fin 2 → ℝ) (Bool × Bool) where
  ν := Measure.count
  Θ := {θ | θ 0 ∈ Set.Ioo 0 1 ∧ θ 1 ∈ Set.Ioo 0 1}
  density θ x := bernoulli.density (θ 0) x.1 * bernoulli.density (θ 1) x.2
  measurable_density _ := .of_discrete
  density_nonneg θ hθ x := mul_nonneg (bernoulli.density_nonneg _ hθ.1 _)
    (bernoulli.density_nonneg _ hθ.2 _)
  integrable_density _ _ := Integrable.of_finite
  integral_density θ _ := by
    simp [Fintype.sum_prod_type, bernoulli_density]
    ring

/-- The counting measure on `Bool × Bool` is finite. -/
instance : IsFiniteMeasure bernoulliPair.ν :=
  inferInstanceAs (IsFiniteMeasure (Measure.count : Measure (Bool × Bool)))

/-- The density of the pair. -/
theorem bernoulliPair_density (θ : Fin 2 → ℝ) (x : Bool × Bool) :
    bernoulliPair.density θ x = bernoulli.density (θ 0) x.1 * bernoulli.density (θ 1) x.2 := rfl

/-- The parameter set is open. -/
theorem isOpen_bernoulliPair_Θ : IsOpen bernoulliPair.Θ :=
  (isOpen_Ioo.preimage (continuous_apply 0)).inter (isOpen_Ioo.preimage (continuous_apply 1))

/-- Expectation under the law of the pair. -/
theorem bernoulliPair_integral_law {θ : Fin 2 → ℝ} (hθ : θ ∈ bernoulliPair.Θ)
    (h : Bool × Bool → ℝ) :
    ∫ x, h x ∂bernoulliPair.law θ =
      θ 0 * θ 1 * h (true, true) + θ 0 * (1 - θ 1) * h (true, false) +
        (1 - θ 0) * θ 1 * h (false, true) + (1 - θ 0) * (1 - θ 1) * h (false, false) := by
  rw [integral_law hθ]
  change ∫ x, bernoulliPair.density θ x * h x ∂(Measure.count : Measure (Bool × Bool)) = _
  simp [Fintype.sum_prod_type, bernoulliPair_density, bernoulli_density]
  ring

/-- The Bernoulli density has derivative `1` at a success and `-1` at a failure. -/
theorem bernoulli_hasDerivAt (u : ℝ) (b : Bool) :
    HasDerivAt (fun v ↦ bernoulli.density v b) (if b then 1 else -1) u := by
  cases b
  · simpa [bernoulli_density] using (hasDerivAt_id' u).const_sub 1
  · simpa [bernoulli_density] using hasDerivAt_id' u

/-- The partial derivative in the first parameter. -/
theorem bernoulliPair_partialDeriv_zero (η : Fin 2 → ℝ) (x : Bool × Bool) :
    bernoulliPair.partialDeriv 0 η x =
      (if x.1 then 1 else -1) * bernoulli.density (η 1) x.2 := by
  have h : (fun t ↦ bernoulliPair.density (Function.update η 0 t) x) =
      fun t ↦ bernoulli.density t x.1 * bernoulli.density (η 1) x.2 := by
    funext t
    simp [bernoulliPair_density]
  rw [partialDeriv, h]
  exact ((bernoulli_hasDerivAt _ _).mul_const _).deriv

/-- The partial derivative in the second parameter. -/
theorem bernoulliPair_partialDeriv_one (η : Fin 2 → ℝ) (x : Bool × Bool) :
    bernoulliPair.partialDeriv 1 η x =
      bernoulli.density (η 0) x.1 * (if x.2 then 1 else -1) := by
  have h : (fun t ↦ bernoulliPair.density (Function.update η 1 t) x) =
      fun t ↦ bernoulli.density (η 0) x.1 * bernoulli.density t x.2 := by
    funext t
    simp [bernoulliPair_density]
  rw [partialDeriv, h]
  exact ((bernoulli_hasDerivAt _ _).const_mul _).deriv

/-- `|±1| = 1`. -/
theorem abs_sign_bool (b : Bool) : |(if b then (1 : ℝ) else -1)| = 1 := by
  cases b <;> simp

/-- The Bernoulli density with a parameter in `(0, 1)` lies in `[0, 1]`. -/
theorem abs_bernoulli_density_le {u : ℝ} (hu : u ∈ Set.Ioo (0 : ℝ) 1) (b : Bool) :
    |bernoulli.density u b| ≤ 1 := by
  rw [abs_of_pos (bernoulli_density_pos hu b), bernoulli_density]
  split_ifs <;> linarith [hu.1, hu.2]

/-- Every second partial derivative of the density is at most `1` in absolute value. -/
theorem abs_bernoulliPair_partialDeriv2_le (j k : Fin 2) (η : Fin 2 → ℝ) (x : Bool × Bool) :
    |bernoulliPair.partialDeriv2 j k η x| ≤ 1 := by
  have h10 : (1 : Fin 2) ≠ 0 := by decide
  fin_cases j <;> fin_cases k
  · have : (fun t ↦ bernoulliPair.partialDeriv 0 (Function.update η 0 t) x) =
        fun _ ↦ (if x.1 then 1 else -1) * bernoulli.density (η 1) x.2 := by
      funext t; rw [bernoulliPair_partialDeriv_zero, Function.update_of_ne h10]
    simp [partialDeriv2, this]
  · have : (fun t ↦ bernoulliPair.partialDeriv 1 (Function.update η 0 t) x) =
        fun t ↦ bernoulli.density t x.1 * (if x.2 then 1 else -1) := by
      funext t; rw [bernoulliPair_partialDeriv_one, Function.update_self]
    change |deriv (fun t ↦ bernoulliPair.partialDeriv 1 (Function.update η 0 t) x) (η 0)| ≤ 1
    rw [this, ((bernoulli_hasDerivAt _ _).mul_const _).deriv]
    rcases x with ⟨_ | _, _ | _⟩ <;> norm_num
  · have : (fun t ↦ bernoulliPair.partialDeriv 0 (Function.update η 1 t) x) =
        fun t ↦ (if x.1 then 1 else -1) * bernoulli.density t x.2 := by
      funext t; rw [bernoulliPair_partialDeriv_zero, Function.update_self]
    change |deriv (fun t ↦ bernoulliPair.partialDeriv 0 (Function.update η 1 t) x) (η 1)| ≤ 1
    rw [this, ((bernoulli_hasDerivAt _ _).const_mul _).deriv]
    rcases x with ⟨_ | _, _ | _⟩ <;> norm_num
  · have : (fun t ↦ bernoulliPair.partialDeriv 1 (Function.update η 1 t) x) =
        fun _ ↦ bernoulli.density (η 0) x.1 * (if x.2 then 1 else -1) := by
      funext t; rw [bernoulliPair_partialDeriv_one, Function.update_of_ne h10.symm]
    simp [partialDeriv2, this]

/-- The density is smooth in the parameter. -/
theorem contDiff_bernoulliPair_density (x : Bool × Bool) :
    ContDiff ℝ 2 fun η : Fin 2 → ℝ ↦ bernoulliPair.density η x := by
  have h : ∀ (i : Fin 2) (b : Bool),
      ContDiff ℝ 2 fun η : Fin 2 → ℝ ↦ bernoulli.density (η i) b := by
    intro i b
    cases b
    · exact contDiff_const.sub (contDiff_apply ℝ (fun _ : Fin 2 ↦ ℝ) i)
    · exact contDiff_apply ℝ (fun _ : Fin 2 ↦ ℝ) i
  exact (h 0 x.1).mul (h 1 x.2)

/-- The ball of radius `ε(θ) = min (min θ₀ (1 - θ₀)) (min θ₁ (1 - θ₁))` around `θ ∈ Θ` lies in
`Θ`. -/
theorem ball_subset_bernoulliPair_Θ {θ : Fin 2 → ℝ} :
    ball θ (min (min (θ 0) (1 - θ 0)) (min (θ 1) (1 - θ 1))) ⊆ bernoulliPair.Θ := by
  intro η hη
  have hi : ∀ i, dist (η i) (θ i) < min (min (θ 0) (1 - θ 0)) (min (θ 1) (1 - θ 1)) :=
    fun i ↦ lt_of_le_of_lt (dist_le_pi_dist η θ i) hη
  have h0 := hi 0
  have h1 := hi 1
  rw [Real.dist_eq, abs_lt] at h0 h1
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩ <;>
    linarith [min_le_left (min (θ 0) (1 - θ 0)) (min (θ 1) (1 - θ 1)),
      min_le_right (min (θ 0) (1 - θ 0)) (min (θ 1) (1 - θ 1)),
      min_le_left (θ 0) (1 - θ 0), min_le_right (θ 0) (1 - θ 0),
      min_le_left (θ 1) (1 - θ 1), min_le_right (θ 1) (1 - θ 1)]

/-- **The pair family is regular at every parameter.** -/
theorem bernoulliPair_isRegularAtVec {θ : Fin 2 → ℝ} (hθ : θ ∈ bernoulliPair.Θ) :
    bernoulliPair.IsRegularAtVec θ := by
  have := isProbabilityMeasure_law hθ
  have hε : 0 < min (min (θ 0) (1 - θ 0)) (min (θ 1) (1 - θ 1)) :=
    lt_min (lt_min hθ.1.1 (by linarith [hθ.1.2])) (lt_min hθ.2.1 (by linarith [hθ.2.2]))
  have hpos : ∀ η ∈ bernoulliPair.Θ, ∀ x, 0 < bernoulliPair.density η x := fun η hη x ↦
    mul_pos (bernoulli_density_pos hη.1 _) (bernoulli_density_pos hη.2 _)
  refine ⟨?_, ⟨_, hε, ball_subset_bernoulliPair_Θ,
    ae_of_all _ fun x ↦ (contDiff_bernoulliPair_density x).contDiffOn, fun _ ↦ 1, fun _ ↦ 1,
    integrable_const _, integrable_const _, ae_of_all _ fun x η hη j k ↦ ⟨?_, ?_⟩⟩,
    fun _ ↦ MemLp.of_discrete⟩
  · filter_upwards [isOpen_bernoulliPair_Θ.mem_nhds hθ] with η hη x
    exact iff_of_true (hpos η hη x) (hpos θ hθ x)
  · have hη' := ball_subset_bernoulliPair_Θ hη
    fin_cases k
    · simp only [Fin.zero_eta, Fin.isValue, bernoulliPair_partialDeriv_zero, abs_mul,
        abs_sign_bool, one_mul]
      exact abs_bernoulli_density_le hη'.2 _
    · simp only [Fin.mk_one, Fin.isValue, bernoulliPair_partialDeriv_one, abs_mul,
        abs_sign_bool, mul_one]
      exact abs_bernoulli_density_le hη'.1 _
  · exact abs_bernoulliPair_partialDeriv2_le j k η x

/-- **The information matrix of the pair** is
`diag(1 / (θ₀ (1 - θ₀)), 1 / (θ₁ (1 - θ₁)))`. -/
theorem bernoulliPair_fisherInfoMatrix {θ : Fin 2 → ℝ} (hθ : θ ∈ bernoulliPair.Θ) :
    bernoulliPair.fisherInfoMatrix θ =
      diagonal ![1 / (θ 0 * (1 - θ 0)), 1 / (θ 1 * (1 - θ 1))] := by
  have a0 : θ 0 ≠ 0 := hθ.1.1.ne'
  have a1 : 1 - θ 0 ≠ 0 := by linarith [hθ.1.2]
  have b0 : θ 1 ≠ 0 := hθ.2.1.ne'
  have b1 : 1 - θ 1 ≠ 0 := by linarith [hθ.2.2]
  ext j k
  fin_cases j <;> fin_cases k <;>
    simp [fisherInfoMatrix, bernoulliPair_integral_law hθ, scoreVec,
      bernoulliPair_partialDeriv_zero, bernoulliPair_partialDeriv_one, bernoulliPair_density,
      bernoulli_density] <;> field_simp <;> ring

/-- The information matrix of the pair is positive definite. -/
theorem bernoulliPair_fisherInfoMatrix_posDef {θ : Fin 2 → ℝ} (hθ : θ ∈ bernoulliPair.Θ) :
    (bernoulliPair.fisherInfoMatrix θ).PosDef := by
  rw [bernoulliPair_fisherInfoMatrix hθ, posDef_diagonal_iff]
  intro i
  fin_cases i
  · exact one_div_pos.2 (mul_pos hθ.1.1 (by linarith [hθ.1.2]))
  · exact one_div_pos.2 (mul_pos hθ.2.1 (by linarith [hθ.2.2]))

/-- The pair of success indicators. -/
noncomputable def successIndicatorPair (x : Bool × Bool) : Fin 2 → ℝ :=
  ![successIndicator x.1, successIndicator x.2]

/-- The pair of success indicators is an unbiased estimator of `θ`. -/
theorem bernoulliPair_isUnbiasedVec : bernoulliPair.IsUnbiasedVec successIndicatorPair := by
  intro θ hθ i
  have := isProbabilityMeasure_law hθ
  refine ⟨Integrable.of_finite, ?_⟩
  rw [mean, bernoulliPair_integral_law hθ]
  fin_cases i <;> simp [successIndicatorPair, successIndicator] <;> ring

/-- **The pair of success indicators attains the matrix Cramér-Rao bound.** At every `θ ∈ Θ`,
`Cov_θ(T) - I(θ)⁻¹` is positive semidefinite (by `IsRegularAtVec.cramer_rao_matrix_of_bounded`,
every hypothesis discharged), and in fact `Cov_θ(T) = I(θ)⁻¹`. -/
theorem bernoulliPair_cramer_rao_matrix_attained {θ : Fin 2 → ℝ} (hθ : θ ∈ bernoulliPair.Θ) :
    (covMatrix (bernoulliPair.law θ) (fun i x ↦ successIndicatorPair x i) -
        (bernoulliPair.fisherInfoMatrix θ)⁻¹).PosSemidef ∧
      covMatrix (bernoulliPair.law θ) (fun i x ↦ successIndicatorPair x i) =
        (bernoulliPair.fisherInfoMatrix θ)⁻¹ := by
  have := isProbabilityMeasure_law hθ
  refine ⟨((bernoulliPair_isRegularAtVec hθ).cramer_rao_matrix_of_bounded
    (bernoulliPair_fisherInfoMatrix_posDef hθ) bernoulliPair_isUnbiasedVec
    (fun _ ↦ .of_discrete) (C := 1) fun x i ↦ ?_).2, ?_⟩
  · obtain ⟨a, b⟩ := x
    fin_cases i <;> cases a <;> cases b <;> simp [successIndicatorPair, successIndicator]
  · have a0 : θ 0 ≠ 0 := hθ.1.1.ne'
    have a1 : 1 - θ 0 ≠ 0 := by linarith [hθ.1.2]
    have b0 : θ 1 ≠ 0 := hθ.2.1.ne'
    have b1 : 1 - θ 1 ≠ 0 := by linarith [hθ.2.2]
    have hm : ∀ i, MemLp (fun x : Bool × Bool ↦ successIndicatorPair x i) 2
        (bernoulliPair.law θ) := fun _ ↦ MemLp.of_discrete
    have hC : covMatrix (bernoulliPair.law θ) (fun i x ↦ successIndicatorPair x i) =
        diagonal ![θ 0 * (1 - θ 0), θ 1 * (1 - θ 1)] := by
      ext j k
      simp only [covMatrix, of_apply, covariance_eq_sub (hm j) (hm k)]
      fin_cases j <;> fin_cases k <;>
        simp [bernoulliPair_integral_law hθ, successIndicatorPair, successIndicator] <;> ring
    rw [hC, bernoulliPair_fisherInfoMatrix hθ]
    refine (inv_eq_left_inv ?_).symm
    rw [diagonal_mul_diagonal, ← diagonal_one]
    congr 1
    ext i
    fin_cases i <;> simp <;> field_simp

/-- **The gradient Cramér-Rao bound for the first success indicator**: its mean is `θ₀`, with
gradient `(1, 0)`, and `∇gᵀ I(θ)⁻¹ ∇g ≤ Var_θ(T₁)` holds by
`IsRegularAtVec.cramer_rao_gradient_of_bounded`. -/
theorem bernoulliPair_cramer_rao_gradient {θ : Fin 2 → ℝ} (hθ : θ ∈ bernoulliPair.Θ) :
    bernoulliPair.gradMean (fun x ↦ successIndicator x.1) θ ⬝ᵥ
        ((bernoulliPair.fisherInfoMatrix θ)⁻¹ *ᵥ
          bernoulliPair.gradMean (fun x ↦ successIndicator x.1) θ) ≤
      Var[fun x ↦ successIndicator x.1; bernoulliPair.law θ] :=
  (bernoulliPair_isRegularAtVec hθ).cramer_rao_gradient_of_bounded
    (bernoulliPair_fisherInfoMatrix_posDef hθ) .of_discrete (C := 1)
    fun x ↦ by obtain ⟨a, b⟩ := x; cases a <;> simp [successIndicator]

end ParametricFamily

end CausalInference
