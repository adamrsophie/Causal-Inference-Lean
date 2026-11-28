/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.Estimation.HajekRegularLinear
public import CausalInference.Estimation.HajekConvolutionInefficient
public import CausalInference.Estimation.ProductFamilyRegular

/-!
# Regular and non regular asymptotically linear estimators: instances

Instances of the covariance criterion `E[φ s] = 1` for Hájek regularity of an asymptotically
linear estimator (`isHajekRegular_of_integral_mul_score_eq_one`,
`exists_isHajekRegular_iff_integral_mul_score_eq_one`), with every hypothesis verified.

## Main results

* `halfShrinkMean`: the Bernoulli proportion shrunk halfway toward `p₀`. It is consistent and
  asymptotically linear at `p₀` with influence function `(x - p₀) / 2`, but `E[φ s] = 1/2`, so it
  is not regular (`halfShrinkMean_not_isHajekRegular`). Under `p₀ + h/√n` its limit law is
  `N(-h/2, p₀ (1 - p₀) / 4)` (`halfShrinkMean_tendsto`); at `p₀ = 1/4` this is `N(-h/2, 3/64)`,
  below the bound `3/16` (`halfShrinkMean_tendsto_quarter`).
* `bernoulli_pi_isRegularAt'`, `bernoulli_pi_isScoreRegular'`, `bernoulli_pi_fisherInfo'`: the
  regularity of the Bernoulli sample family obtained from the general transfer lemmas
  `pi_isRegularAt`, `pi_isScoreRegular_of_discrete` and `pi_fisherInfo_of_isRegularAt`.
* `firstCoordMean_isHajekRegular_of_integral_mul_score`: in the family of Bernoulli pairs the
  mean of the first coordinates has influence function `x₁ - p₀` with `E[φ s] = 1`, hence is
  regular with limit `N(0, p₀ (1 - p₀))`.
* `firstCoord_excess`: its inefficient part `φ - I⁻¹ s` is orthogonal to the score with second
  moment `p₀ (1 - p₀) / 2`; `firstCoord_quarter` gives the values `3/16`, `3/32`, `3/32` at
  `p₀ = 1/4`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Finset Metric
open scoped Topology ENNReal NNReal BoundedContinuousFunction

namespace CausalInference

namespace ParametricFamily

variable {p₀ : ℝ}

/-! ### A consistent asymptotically linear estimator that is not regular -/

/-- The sample proportion shrunk halfway toward a fixed value `p₀`: `(p̂_n + p₀) / 2`. -/
noncomputable def halfShrinkMean (p₀ : ℝ) (n : ℕ) (x : Fin n → Bool) : ℝ :=
  (bernoulliSampleMean n x + p₀) / 2

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
  {O : ℕ → Ω → Bool}

/-- **The shrunk proportion is asymptotically linear** at `p₀` with influence function
`(x - p₀) / 2`, on an i.i.d. Bernoulli(`p₀`) sample. -/
theorem halfShrinkMean_isAsymptoticallyLinear (hO : IsIIDSample O μ)
    (hlaw : μ.map (O 0) = bernoulli.law p₀) (hp : p₀ ∈ Set.Ioo (0 : ℝ) 1) :
    IsAsymptoticallyLinear (fun n ω ↦ halfShrinkMean p₀ n fun i ↦ O i ω) p₀
      (fun x ↦ 1 / 2 * (successIndicator x - p₀)) O μ := by
  have h := (bernoulliSampleMean_isAsymptoticallyLinear hO hlaw hp).const_mul (1 / 2)
  have e : (fun x ↦ 1 / 2 * (successIndicator x - p₀)) =
      fun x ↦ 1 / 2 * ((bernoulli.fisherInfo p₀)⁻¹ * bernoulli.score p₀ x) :=
    funext fun x ↦ by rw [bernoulli_inv_fisherInfo_mul_score hp]
  rw [e]
  refine ⟨h.measurable, h.memLp, h.integral_eq_zero, ?_⟩
  refine h.remainder.congr' (Eventually.of_forall fun n ↦ Eventually.of_forall fun ω ↦ ?_)
    EventuallyEq.rfl
  simp only [halfShrinkMean]
  ring

/-- The shrunk proportion is consistent at `p₀`. -/
theorem halfShrinkMean_isConsistent (hO : IsIIDSample O μ)
    (hlaw : μ.map (O 0) = bernoulli.law p₀) (hp : p₀ ∈ Set.Ioo (0 : ℝ) 1) :
    IsConsistent (fun n ω ↦ halfShrinkMean p₀ n fun i ↦ O i ω) p₀ μ :=
  (halfShrinkMean_isAsymptoticallyLinear hO hlaw hp).isConsistent hO

/-- The influence function `(x - p₀) / 2` has covariance `1/2` with the score. -/
theorem halfShrink_integral_mul_score (hp : p₀ ∈ Set.Ioo (0 : ℝ) 1) :
    ∫ x, 1 / 2 * (successIndicator x - p₀) * bernoulli.score p₀ x ∂bernoulli.law p₀ = 1 / 2 := by
  simp_rw [← bernoulli_inv_fisherInfo_mul_score hp]
  simp_rw [mul_assoc (1 / 2 : ℝ)]
  rw [integral_const_mul,
    integral_inv_fisherInfo_mul_score_mul_score (bernoulli_fisherInfo_pos hp), mul_one]

/-- The influence function `(x - p₀) / 2` has second moment `p₀ (1 - p₀) / 4`. -/
theorem halfShrink_integral_sq (hp : p₀ ∈ Set.Ioo (0 : ℝ) 1) :
    ∫ x, (1 / 2 * (successIndicator x - p₀)) ^ 2 ∂bernoulli.law p₀ = p₀ * (1 - p₀) / 4 := by
  simp_rw [← bernoulli_inv_fisherInfo_mul_score hp]
  simp_rw [mul_pow]
  rw [integral_const_mul, integral_const_mul, ← fisherInfo, bernoulli_inv_fisherInfo hp]
  have h1 : 1 - p₀ ≠ 0 := by linarith [hp.2]
  have h0 : p₀ ≠ 0 := hp.1.ne'
  rw [bernoulli_fisherInfo hp]
  field_simp
  ring

/-- **The limit law of the shrunk proportion under local alternatives**: under `p₀ + h/√n`,
`√n (T_n - p₀ - h/√n)` converges weakly to `N(-h/2, p₀ (1 - p₀) / 4)`, which depends on `h`. -/
theorem halfShrinkMean_tendsto (hp : p₀ ∈ Set.Ioo (0 : ℝ) 1) (h : ℝ) (f : ℝ →ᵇ ℝ) :
    Tendsto (fun n : ℕ ↦ ∫ x, f (√(n : ℝ) * (halfShrinkMean p₀ n x - (p₀ + h / √(n : ℝ))))
      ∂(bernoulli.pi n).law (p₀ + h / √(n : ℝ))) atTop
      (𝓝 (∫ y, f y ∂gaussianReal (-h / 2) (p₀ * (1 - p₀) / 4).toNNReal)) := by
  have := isProbabilityMeasure_law (F := bernoulli) hp
  obtain ⟨Ω', _, P', O', hP', -, hO', hlaw'⟩ := exists_isIIDSample (bernoulli.law p₀)
  have key := tendsto_integral_pi_law_of_isAsymptoticallyLinear hO' (hlaw' 0).map_eq
    (bernoulli_isRegularAt hp) (bernoulli_isScoreRegular hp)
    (bernoulli_hasDerivAt_logLik_closedBall hp) (bernoulli_fisherInfo_pos hp)
    (fun _ ↦ .of_discrete) (halfShrinkMean_isAsymptoticallyLinear hO' (hlaw' 0).map_eq hp) h f
  rw [halfShrink_integral_mul_score hp, halfShrink_integral_sq hp] at key
  convert key using 3
  congr 1
  ring

/-- **The shrunk proportion is not regular**: it is consistent and asymptotically linear at
`p₀`, but `E[φ s] = 1/2 ≠ 1`, so no limit law makes it regular in Hájek's sense. Its limit
variance `p₀ (1 - p₀) / 4` is below the bound `p₀ (1 - p₀)`: the bound holds only for regular
estimators. -/
theorem halfShrinkMean_not_isHajekRegular (hp : p₀ ∈ Set.Ioo (0 : ℝ) 1) :
    ¬ ∃ L : Measure ℝ, bernoulli.IsHajekRegular (halfShrinkMean p₀) p₀ L := by
  have := isProbabilityMeasure_law (F := bernoulli) hp
  obtain ⟨Ω', _, P', O', hP', -, hO', hlaw'⟩ := exists_isIIDSample (bernoulli.law p₀)
  rw [exists_isHajekRegular_iff_integral_mul_score_eq_one hO' (hlaw' 0).map_eq
    (bernoulli_isRegularAt hp) (bernoulli_isScoreRegular hp)
    (bernoulli_hasDerivAt_logLik_closedBall hp) (bernoulli_fisherInfo_pos hp)
    (fun _ ↦ .of_discrete) (halfShrinkMean_isAsymptoticallyLinear hO' (hlaw' 0).map_eq hp),
    halfShrink_integral_mul_score hp]
  norm_num

/-- At `p₀ = 1/4` the shrunk proportion has limit `N(-h/2, 3/64)` under `1/4 + h/√n`, below the
bound `3/16`. -/
theorem halfShrinkMean_tendsto_quarter (h : ℝ) (f : ℝ →ᵇ ℝ) :
    Tendsto (fun n : ℕ ↦ ∫ x, f (√(n : ℝ) * (halfShrinkMean (1 / 4) n x - (1 / 4 + h / √(n : ℝ))))
      ∂(bernoulli.pi n).law (1 / 4 + h / √(n : ℝ))) atTop
      (𝓝 (∫ y, f y ∂gaussianReal (-h / 2) (3 / 64 : ℝ).toNNReal)) ∧
      (3 / 64 : ℝ) < (bernoulli.fisherInfo (1 / 4))⁻¹ := by
  refine ⟨?_, by rw [bernoulli_fisherInfo_quarter]; norm_num⟩
  have := halfShrinkMean_tendsto (p₀ := 1 / 4) ⟨by norm_num, by norm_num⟩ h f
  norm_num at this ⊢
  exact this

/-! ### The Bernoulli sample family through the general transfer lemmas -/

/-- The Bernoulli sample family is regular at every `p₀ ∈ (0, 1)`, as an instance of
`pi_isRegularAt` (compare `bernoulli_pi_isRegularAt`). -/
theorem bernoulli_pi_isRegularAt' (n : ℕ) (hp : p₀ ∈ Set.Ioo (0 : ℝ) 1) :
    (bernoulli.pi n).IsRegularAt p₀ :=
  pi_isRegularAt n (bernoulli_isRegularAt hp)

/-- The Bernoulli sample family has smooth score near `p₀`, with the derivative identity, as an
instance of `pi_isScoreRegular_of_discrete` (compare `bernoulli_pi_isScoreRegular` and
`bernoulli_pi_hasDerivAt_logLik_closedBall`, which give the radius `min p₀ (1 - p₀) / 2`). -/
theorem bernoulli_pi_isScoreRegular' (n : ℕ) (hp : p₀ ∈ Set.Ioo (0 : ℝ) 1) :
    ∃ r' ∈ Set.Ioc 0 (min p₀ (1 - p₀) / 2), (bernoulli.pi n).IsScoreRegular p₀ r' ∧
      ∀ᵐ x ∂(bernoulli.pi n).law p₀, ∀ θ ∈ closedBall p₀ r',
        HasDerivAt (fun u ↦ (bernoulli.pi n).logLik u x) ((bernoulli.pi n).score θ x) θ :=
  pi_isScoreRegular_of_discrete n (bernoulli_isRegularAt hp) (bernoulli_isScoreRegular hp)
    (bernoulli_hasDerivAt_logLik_closedBall hp)

/-- The information of a Bernoulli sample of size `n` is `n / (p₀ (1 - p₀))`, as an instance of
`pi_fisherInfo_of_isRegularAt` (compare `bernoulli_pi_fisherInfo`). -/
theorem bernoulli_pi_fisherInfo' (n : ℕ) (hp : p₀ ∈ Set.Ioo (0 : ℝ) 1) :
    (bernoulli.pi n).fisherInfo p₀ = n / (p₀ * (1 - p₀)) := by
  rw [pi_fisherInfo_of_isRegularAt n (bernoulli_isRegularAt hp), bernoulli_fisherInfo hp,
    mul_one_div]

/-! ### The first coordinate mean of pairs, through the covariance criterion -/

/-- Under the pair family a function of the first coordinate has its Bernoulli integral. -/
lemma pair_integral_comp_fst (hp : p₀ ∈ Set.Ioo (0 : ℝ) 1) (g : Bool → ℝ) :
    ∫ x, g (x 0) ∂(bernoulli.pi 2).law p₀ = ∫ b, g b ∂bernoulli.law p₀ := by
  have := isProbabilityMeasure_law (F := bernoulli) hp
  have h := integral_map (μ := Measure.pi fun _ : Fin 2 ↦ bernoulli.law p₀)
    (measurable_pi_apply 0).aemeasurable (Measurable.of_discrete (f := g)).aestronglyMeasurable
  rw [(measurePreserving_eval (fun _ : Fin 2 ↦ bernoulli.law p₀) 0).map_eq] at h
  rw [pi_law (F := bernoulli) 2 hp, ← h]

/-- **The first coordinate influence function has unit covariance with the pair score**:
`E[(x₁ - p₀) (s(x₁) + s(x₂))] = 1 + E[x₁ - p₀] E[s(x₂)] = 1`. -/
theorem firstCoord_integral_mul_score (hp : p₀ ∈ Set.Ioo (0 : ℝ) 1) :
    ∫ x, (successIndicator (x 0) - p₀) * (bernoulli.pi 2).score p₀ x
      ∂(bernoulli.pi 2).law p₀ = 1 := by
  have := isProbabilityMeasure_law (F := bernoulli) hp
  have := isProbabilityMeasure_law (F := bernoulli.pi 2) hp
  set g : Bool → ℝ := fun b ↦ successIndicator b - p₀ with hg
  set k : Fin 2 → Bool → ℝ := ![g, bernoulli.score p₀] with hk
  have hsplit : (fun x : Fin 2 → Bool ↦ (successIndicator (x 0) - p₀) *
      (bernoulli.pi 2).score p₀ x) =
      fun x ↦ g (x 0) * bernoulli.score p₀ (x 0) + ∏ i, k i (x i) := by
    funext x
    rw [bernoulli_pi_score hp, Fin.sum_univ_two, Fin.prod_univ_two]
    simp only [hk, hg, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
    ring
  have h1 : ∫ x, g (x 0) * bernoulli.score p₀ (x 0) ∂(bernoulli.pi 2).law p₀ = 1 := by
    rw [pair_integral_comp_fst hp (fun b ↦ g b * bernoulli.score p₀ b), hg]
    simp_rw [← bernoulli_inv_fisherInfo_mul_score hp]
    exact integral_inv_fisherInfo_mul_score_mul_score (bernoulli_fisherInfo_pos hp)
  have h2 : ∫ x, ∏ i, k i (x i) ∂(bernoulli.pi 2).law p₀ = 0 := by
    rw [pi_law (F := bernoulli) 2 hp, integral_fintype_prod_eq_prod (f := k), Fin.prod_univ_two]
    simp only [hk, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
    rw [(bernoulli_isRegularAt hp).integral_score_eq_zero, mul_zero]
  rw [hsplit, integral_add Integrable.of_finite Integrable.of_finite, h1, h2, add_zero]

/-- The first coordinate influence function has second moment `p₀ (1 - p₀)`. -/
theorem firstCoord_integral_sq (hp : p₀ ∈ Set.Ioo (0 : ℝ) 1) :
    ∫ x, (successIndicator (x 0) - p₀) ^ 2 ∂(bernoulli.pi 2).law p₀ = p₀ * (1 - p₀) := by
  rw [pair_integral_comp_fst hp (fun b ↦ (successIndicator b - p₀) ^ 2)]
  simp_rw [← bernoulli_inv_fisherInfo_mul_score hp, mul_pow]
  rw [integral_const_mul, ← fisherInfo, bernoulli_inv_fisherInfo hp]
  have h1 : 1 - p₀ ≠ 0 := by linarith [hp.2]
  have h0 : p₀ ≠ 0 := hp.1.ne'
  rw [bernoulli_fisherInfo hp]
  field_simp

/-- **The first coordinate mean is regular, by the covariance criterion**: it is asymptotically
linear with influence function `x₁ - p₀`, which has unit covariance with the pair score, so it is
regular with limit `N(0, E[(x₁ - p₀)²]) = N(0, p₀ (1 - p₀))`
(`isHajekRegular_of_integral_mul_score_eq_one`). -/
theorem firstCoordMean_isHajekRegular_of_integral_mul_score (hp : p₀ ∈ Set.Ioo (0 : ℝ) 1) :
    (bernoulli.pi 2).IsHajekRegular firstCoordMean p₀
      (gaussianReal 0 (p₀ * (1 - p₀)).toNNReal) := by
  have := isProbabilityMeasure_law (F := bernoulli.pi 2) hp
  obtain ⟨Ω', _, P', O', hP', -, hO', hlaw'⟩ := exists_isIIDSample ((bernoulli.pi 2).law p₀)
  rw [← firstCoord_integral_sq hp]
  exact isHajekRegular_of_integral_mul_score_eq_one hO' (hlaw' 0).map_eq
    (bernoulli_pi_isRegularAt 2 hp) (bernoulli_pi_isScoreRegular 2 hp)
    (bernoulli_pi_hasDerivAt_logLik_closedBall 2 hp) (fisherInfo_pair_pos hp)
    (fun _ ↦ .of_discrete) (firstCoordMean_isAsymptoticallyLinear hO' (hlaw' 0).map_eq hp)
    (firstCoord_integral_mul_score hp)

/-- **The excess of the first coordinate mean over the bound**: the inefficient part
`φ - I⁻¹ s` of its influence function is orthogonal to the score and has second moment
`p₀ (1 - p₀) / 2`, the difference between the limit variance `p₀ (1 - p₀)` and the bound
`p₀ (1 - p₀) / 2`. -/
theorem firstCoord_excess (hp : p₀ ∈ Set.Ioo (0 : ℝ) 1) :
    ∫ x, (successIndicator (x 0) - p₀ - ((bernoulli.pi 2).fisherInfo p₀)⁻¹ *
        (bernoulli.pi 2).score p₀ x) * (bernoulli.pi 2).score p₀ x ∂(bernoulli.pi 2).law p₀ = 0 ∧
      ∫ x, (successIndicator (x 0) - p₀ - ((bernoulli.pi 2).fisherInfo p₀)⁻¹ *
        (bernoulli.pi 2).score p₀ x) ^ 2 ∂(bernoulli.pi 2).law p₀ = p₀ * (1 - p₀) / 2 := by
  have := isProbabilityMeasure_law (F := bernoulli.pi 2) hp
  obtain ⟨h1, h2⟩ := integral_sub_inv_fisherInfo_mul_score (bernoulli_pi_isRegularAt 2 hp)
    (fisherInfo_pair_pos hp) (φ := fun x ↦ successIndicator (x 0) - p₀) MemLp.of_discrete
    (firstCoord_integral_mul_score hp)
  refine ⟨h1, ?_⟩
  rw [h2, firstCoord_integral_sq hp, inv_fisherInfo_pair hp]
  ring

/-- At `p₀ = 1/4` the first coordinate mean has limit variance `3/16`, the bound is `3/32`, and
the excess `E[(φ - I⁻¹ s)²]` is `3/32`. -/
theorem firstCoord_quarter :
    ∫ x, (successIndicator (x 0) - 1 / 4) ^ 2 ∂(bernoulli.pi 2).law (1 / 4) = 3 / 16 ∧
      ((bernoulli.pi 2).fisherInfo (1 / 4))⁻¹ = 3 / 32 ∧
      ∫ x, (successIndicator (x 0) - 1 / 4 - ((bernoulli.pi 2).fisherInfo (1 / 4))⁻¹ *
        (bernoulli.pi 2).score (1 / 4) x) ^ 2 ∂(bernoulli.pi 2).law (1 / 4) = 3 / 32 := by
  have hq : (1 / 4 : ℝ) ∈ Set.Ioo (0 : ℝ) 1 := ⟨by norm_num, by norm_num⟩
  refine ⟨by rw [firstCoord_integral_sq hq]; norm_num, inv_fisherInfo_pair_quarter, ?_⟩
  rw [(firstCoord_excess hq).2]
  norm_num

end ParametricFamily

end CausalInference
