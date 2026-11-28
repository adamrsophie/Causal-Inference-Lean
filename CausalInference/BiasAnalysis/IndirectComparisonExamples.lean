/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.BiasAnalysis.IndirectComparisonBound
public import CausalInference.BiasAnalysis.IndirectComparisonFiniteConfounder
public import CausalInference.BiasAnalysis.IndirectComparisonTippingPoint
public import CausalInference.BiasAnalysis.IndirectComparisonArcsine

/-!
# Numerical instances for the bias analysis of indirect comparisons

Concrete values for the results of `IndirectComparisonEValue`, `IndirectComparisonBound`,
`IndirectComparisonFiniteConfounder`, `IndirectComparisonTippingPoint`,
`IndirectComparisonRankCorrelation` and `IndirectComparisonArcsine`.

* `eValue_two`: `eValue 2 = 2 + √2`; with `isLeast_eValue`, `2 + √2` is the least common
  strength explaining away a risk ratio of `2` (`isLeast_two_add_sqrt_two`).
* `indirect_eValue_four`: an observed indirect risk ratio of `4` has indirect E-value
  `eValue √4 = 2 + √2`, attained by `anchored_explainAway_attained` (`indirect_four_attained`).
* `eValue_inv_two`: the protective ratio `1/2` has the same E-value `2 + √2`.
* `unanchored_instance`: a numerical instance of `unanchored_indirect_bias_le`.
* `requiredStrength_two_four`: with outcome strength `4`, a ratio of `2` needs exposure
  strength `3`.
* `finite_instance`: a three level confounder with bias factor `9/8` against the bound
  `boundingFactor 2 2 = 4/3`.
* `finiteBiasFactor_two_three`: the finite bound `boundingFactor 2 3 = 3/2` is attained.
* `tipping_linear_instance`: an estimate `1/2` with interaction coefficient `1/4` tips at
  `D = 2`; `tipping_affine_instance`: `1 - t` first fails `> 0` at `t = 1`.
* `tipping_not_unique`: `t² - 1` has the two roots `±1`; `existsUnique_tipping_instance`.
* `anchored_explainAway_four`, `eValue_two_lt_four`, `eValueLimit_instance`,
  `one_lt_div_instance`: instances of `anchored_explainAway_le`, `eValue_lt_max_of_ne`,
  `isLeast_eValue_max` and the confidence limit results.
* `rankCorrelation_half`: a Gaussian pair with `ρ = 2 sin(π/12)` has rank correlation `1/2`;
  `rankCorrelation_exp_half`: it stays `1/2` after `V ↦ exp V`.
* `finite_eValue_instance`, `ratio_outcomeStrength_instance`: instances of
  `finite_eValue_le_max` and `ratio_le_outcomeStrength` on three levels.
-/

@[expose] public section

namespace CausalInference

namespace BiasAnalysis

namespace IndirectComparisonBias

open Set BiasFormulas ExternalAdjustment

open scoped Real

/-- `eValue 2 = 2 + √2`. -/
theorem eValue_two : eValue 2 = 2 + Real.sqrt 2 := by
  rw [eValue_of_one_le (by norm_num)]
  norm_num

/-- `2 + √2` is the least common strength `v ≥ 1` with `2 ≤ boundingFactor v v`. -/
theorem isLeast_two_add_sqrt_two :
    IsLeast {v | 1 ≤ v ∧ 2 ≤ boundingFactor v v} (2 + Real.sqrt 2) := by
  rw [← eValue_two]
  exact isLeast_eValue (by norm_num)

/-- The indirect E-value of an observed indirect ratio `4` is `eValue √4 = 2 + √2`. -/
theorem indirect_eValue_four : eValue (Real.sqrt 4) = 2 + Real.sqrt 2 := by
  rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num), eValue_two]

/-- For an observed indirect ratio `4`, the least common strength `v` with
`4 ≤ boundingFactor v v ^ 2` is `2 + √2`, and the configuration of
`anchored_explainAway_attained` with this strength gives observed ratio exactly `4` with no
effect within levels of the confounder. -/
theorem indirect_four_attained :
    IsLeast {v | 1 ≤ v ∧ 4 ≤ boundingFactor v v * boundingFactor v v} (2 + Real.sqrt 2) ∧
      let E := eValue (Real.sqrt 4)
      crudeRR (fun _ u => cond u E 1) (fun a => cond a 1 E⁻¹) /
        crudeRR (fun _ u => cond u E 1) (fun a => cond a E⁻¹ 1) = 4 := by
  refine ⟨?_, ?_⟩
  · rw [← indirect_eValue_four]
    exact isLeast_eValue_sqrt (by norm_num)
  · exact (anchored_explainAway_attained (by norm_num : (1 : ℝ) < 4)).2.2.2.2.2.2.2.2.2.2.2.2.2

/-- The protective ratio `1/2` has E-value `2 + √2`. -/
theorem eValue_inv_two : eValue (1 / 2) = 2 + Real.sqrt 2 := by
  rw [one_div, eValue_inv, eValue_two]

/-- **A numerical unanchored instance.** Arm `A` has stratum risks `(0.1, 0.3)`, arm `B`
`(0.2, 0.4)`; the sources have covariate prevalences `p₁ = 0.6` and `p₂ = 0.3`, the target
`q = 0.4`. The observed ratio over the target ratio is at most the product of the two bounding
factors. -/
theorem unanchored_instance :
    let RA : Bool → ℝ := fun u => cond u (3 / 10) (1 / 10)
    let RB : Bool → ℝ := fun u => cond u (4 / 10) (2 / 10)
    (prevMean RA (6 / 10) / prevMean RB (3 / 10)) / (prevMean RA (4 / 10) / prevMean RB (4 / 10))
      ≤ boundingFactor (max (RA true / RA false) (RA false / RA true))
          (max ((6 / 10) / (4 / 10)) ((1 - 6 / 10) / (1 - 4 / 10))) *
        boundingFactor (max (RB true / RB false) (RB false / RB true))
          (max ((4 / 10) / (3 / 10)) ((1 - 4 / 10) / (1 - 3 / 10))) :=
  unanchored_indirect_bias_le (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- With outcome strength `4`, a ratio `2` is explained away by an exposure strength of exactly
`3` and by nothing smaller: `boundingFactor 3 4 = 2`. -/
theorem requiredStrength_two_four :
    requiredStrength 2 4 = 3 ∧ IsLeast {x | 1 ≤ x ∧ 2 ≤ boundingFactor x 4} 3 := by
  have h : requiredStrength 2 4 = 3 := by norm_num [requiredStrength]
  refine ⟨h, ?_⟩
  rw [← h]
  exact isLeast_requiredStrength (by norm_num) (by norm_num)

/-- **A three level confounder.** Stratum risks `p₀ = (0.1, 0.2, 0.2)`, confounder laws
`f₁ = (0.2, 0.4, 0.4)` and `f₀ = (0.4, 0.4, 0.2)`: the bias factor `0.18 / 0.16 = 9/8` is at most
`boundingFactor RR_EU RR_UD`. -/
theorem finite_instance :
    finiteBiasFactor ![1 / 10, 2 / 10, 2 / 10] ![2 / 10, 4 / 10, 4 / 10] ![4 / 10, 4 / 10, 2 / 10]
        = 9 / 8 ∧
      finiteBiasFactor ![1 / 10, 2 / 10, 2 / 10] ![2 / 10, 4 / 10, 4 / 10]
          ![4 / 10, 4 / 10, 2 / 10] ≤
        boundingFactor (exposureStrength ![2 / 10, 4 / 10, 4 / 10] ![4 / 10, 4 / 10, 2 / 10])
          (outcomeStrength ![(1 : ℝ) / 10, 2 / 10, 2 / 10]) := by
  refine ⟨?_, finiteBiasFactor_le_boundingFactor ?_ ?_ ?_ ?_ ?_⟩
  · simp only [finiteBiasFactor, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons]
    norm_num
  all_goals first
    | (intro u; fin_cases u <;> norm_num)
    | (simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons]; norm_num)

/-- The finite bound is attained at `RR_EU = 2`, `RR_UD = 3`, where it is `3/2`. -/
theorem finiteBiasFactor_two_three :
    ∃ p₀ f₁ f₀ : Fin 2 → ℝ, (∀ u, 0 < p₀ u) ∧ (∀ u, 0 ≤ f₁ u) ∧ ∑ u, f₁ u = 1 ∧
      (∀ u, 0 < f₀ u) ∧ ∑ u, f₀ u = 1 ∧ exposureStrength f₁ f₀ = 2 ∧
      outcomeStrength p₀ = 3 ∧ finiteBiasFactor p₀ f₁ f₀ = 3 / 2 := by
  have h : boundingFactor 2 3 = 3 / 2 := by norm_num [boundingFactor]
  rw [← h]
  exact finiteBiasFactor_attained (by norm_num) (by norm_num)

/-- **A linear tipping point.** An estimate `θ = 1/2` with interaction coefficient `κ = 1/4`
reaches the null at the imbalance `D = 2`, and `2` is the least imbalance that does so. -/
theorem tipping_linear_instance :
    (∀ D : ℝ, 1 / 2 - D * (1 / 4) = 0 ↔ D = 2) ∧
      IsLeast {s | 0 ≤ s ∧ ∃ D, |D| = s ∧ (1 : ℝ) / 2 - D * (1 / 4) ≤ 0} 2 := by
  have h := isLeast_tipping_linear (θ := 1 / 2) (c := 0) (κ := 1 / 4) (by norm_num) (by norm_num)
  have e : ((1 : ℝ) / 2 - 0) / |1 / 4| = 2 := by norm_num [abs_of_pos]
  rw [e] at h
  refine ⟨fun D => ?_, h⟩
  rw [(tipping_linear (θ := 1 / 2) (c := 0) (κ := 1 / 4) (by norm_num)).2.1 D]
  norm_num

/-- **The least failing magnitude for `1 - t`.** For `Δ t = 1 - t` and `c = 0`, the least
`t ≥ 0` with `Δ t ≤ 0` is `1`. -/
theorem tipping_affine_instance : IsLeast {t : ℝ | 0 ≤ t ∧ 1 - t ≤ 0} 1 := by
  obtain ⟨t₀, ht, -, -⟩ := exists_isLeast_tipping (Δ := fun t : ℝ => 1 - t) (c := 0)
    (by fun_prop) (by norm_num) ⟨1, by norm_num, by norm_num⟩
  have : t₀ = 1 := le_antisymm (ht.2 ⟨by norm_num, by norm_num⟩) (by linarith [ht.1.2])
  rwa [this] at ht

/-- **Without monotonicity a tipping point need not be unique**: `t² - 1` reaches `0` at both
`t = -1` and `t = 1`. -/
theorem tipping_not_unique : (-1 : ℝ) ^ 2 - 1 = 0 ∧ (1 : ℝ) ^ 2 - 1 = 0 ∧ (-1 : ℝ) ≠ 1 := by
  norm_num

/-- **Matching the rank correlation `1/2`.** The Gaussian pair with correlation
`ρ = 2 sin(π/12)` has rank correlation `1/2`. -/
theorem rankCorrelation_half :
    rankCorrelation (fun p : ℝ × ℝ => p.1)
        (fun p => 2 * Real.sin (π * (1 / 2) / 6) * p.1 +
          √(1 - (2 * Real.sin (π * (1 / 2) / 6)) ^ 2) * p.2) stdNormalPair = 1 / 2 := by
  have h := rankCorrelation_gaussian_pair_target (ρS := 1 / 2) ⟨by norm_num, by norm_num⟩
  exact h.2

/-- **The finite E-value condition at a null effect.** With the confounder of `finite_instance`
and exposed risks equal to the unexposed ones (no effect), the observed risk ratio `9/8` can only
come from a confounder with `max RR_EU RR_UD ≥ eValue (9/8)`. -/
theorem finite_eValue_instance :
    eValue (9 / 8) ≤ max (exposureStrength ![2 / 10, 4 / 10, 4 / 10] ![4 / 10, 4 / 10, 2 / 10])
      (outcomeStrength ![(1 : ℝ) / 10, 2 / 10, 2 / 10]) := by
  have h := finite_eValue_le_max (p₀ := ![(1 : ℝ) / 10, 2 / 10, 2 / 10])
    (p₁ := ![(1 : ℝ) / 10, 2 / 10, 2 / 10]) (f₁ := ![2 / 10, 4 / 10, 4 / 10])
    (f₀ := ![4 / 10, 4 / 10, 2 / 10])
  have e : (∑ u, ![(1 : ℝ) / 10, 2 / 10, 2 / 10] u * ![2 / 10, 4 / 10, 4 / 10] u) /
      (∑ u, ![(1 : ℝ) / 10, 2 / 10, 2 / 10] u * ![4 / 10, 4 / 10, 2 / 10] u) = 9 / 8 := by
    simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons]
    norm_num
  rw [e] at h
  refine h ?_ ?_ ?_ ?_ ?_ ?_ (by norm_num)
  all_goals first
    | (intro u; fin_cases u <;> norm_num)
    | (simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons]; norm_num)

/-- **The response range bound on three levels.** For responses `(1, 2, 4)` and the laws
`(0, 1/2, 1/2)` and `(1/2, 1/2, 0)` the ratio of averages is `3 / (3/2) = 2`, at most
`max / min = 4`. -/
theorem ratio_outcomeStrength_instance :
    (∑ u, ![(1 : ℝ), 2, 4] u * ![0, 1 / 2, 1 / 2] u) / (∑ u, ![(1 : ℝ), 2, 4] u *
      ![1 / 2, 1 / 2, 0] u) ≤ outcomeStrength ![(1 : ℝ), 2, 4] := by
  refine ratio_le_outcomeStrength ?_ ?_ ?_ ?_ ?_
  all_goals first
    | (intro u; fin_cases u <;> norm_num)
    | (simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons]; norm_num)

/-- **Rank correlation after a change of scale.** Replacing `V` by `exp V` does not change the
rank correlation `1/2` of `rankCorrelation_half`. -/
theorem rankCorrelation_exp_half :
    rankCorrelation (Real.exp ∘ fun p : ℝ × ℝ => p.1)
        (id ∘ fun p : ℝ × ℝ => 2 * Real.sin (π * (1 / 2) / 6) * p.1 +
          √(1 - (2 * Real.sin (π * (1 / 2) / 6)) ^ 2) * p.2) stdNormalPair = 1 / 2 := by
  rw [rankCorrelation_comp measurable_fst (by fun_prop) Real.exp_strictMono strictMono_id]
  exact rankCorrelation_half

/-- **The attaining configuration satisfies the explain away bound.** The configuration of
`anchored_explainAway_attained` at `RR = 4`, with `w₁ = w₂ = 1` and all four parameters equal to
`E = 2 + √2`, meets every hypothesis of `anchored_explainAway_le`, which gives
`4 ≤ boundingFactor E E * boundingFactor E E`. -/
theorem anchored_explainAway_four :
    let E := eValue (Real.sqrt 4)
    crudeRR (fun _ u => cond u E 1) (fun a => cond a 1 E⁻¹) /
        crudeRR (fun _ u => cond u E 1) (fun a => cond a E⁻¹ 1) ≤
      boundingFactor E E * boundingFactor E E := by
  intro E
  obtain ⟨hm, hL, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, hst, -⟩ :=
    anchored_explainAway_attained (by norm_num : (1 : ℝ) < 4)
  refine anchored_explainAway_le (w₁ := 1) (w₂ := 1) hm h1 h2 zero_le_one h3 zero_le_one le_rfl
    rfl h4 h5 hL hm h6 h7 zero_le_one h8 zero_le_one le_rfl rfl h9 h10 hL ?_
  rw [hst _ (by simp) (by simp), hst _ (by simp) (by simp)]
  norm_num

/-- **A tipping point on an interval.** `Δ t = t` on `[0, 1]` reaches `1/2` at exactly one
point. -/
theorem existsUnique_tipping_instance : ∃! t : ℝ, t ∈ Icc (0 : ℝ) 1 ∧ t = 1 / 2 :=
  (existsUnique_tipping (Δ := id) (c := 1 / 2) zero_le_one continuousOn_id
    (Or.inl (strictMono_id.strictMonoOn _))).1
    (by rw [id, id, uIcc_of_le zero_le_one]; norm_num)

/-- **Unequal strengths exceed the E-value.** For `RR = 2` the pair `(3, 4)` explains the estimate
away (`boundingFactor 3 4 = 2`), and its maximum `4` exceeds `eValue 2 = 2 + √2`; the least
maximum over all pairs is `2 + √2`. -/
theorem eValue_two_lt_four :
    boundingFactor 3 4 = 2 ∧ eValue 2 < max 3 4 ∧
      IsLeast {M | ∃ a b, 1 ≤ a ∧ 1 ≤ b ∧ 2 ≤ boundingFactor a b ∧ M = max a b}
        (2 + Real.sqrt 2) := by
  have h : boundingFactor 3 4 = 2 := by norm_num [boundingFactor]
  refine ⟨h, eValue_lt_max_of_ne (by norm_num) (by norm_num) (by norm_num) h.ge (by norm_num), ?_⟩
  rw [← eValue_two]
  exact isLeast_eValue_max (by norm_num)

/-- **The E-value of a confidence interval.** For the interval `(2, 3)` around `5/2`, the
E-value of the limit is `eValue 2 = 2 + √2`, at most the E-value of the estimate, and a common
strength `E = 2 + √2` moves the lower limit exactly to the null. -/
theorem eValueLimit_instance :
    eValueLimit 2 3 = 2 + Real.sqrt 2 ∧ eValueLimit 2 3 ≤ eValue (5 / 2) ∧
      2 / boundingFactor (eValueLimit 2 3) (eValueLimit 2 3) = 1 := by
  refine ⟨?_, eValueLimit_le_eValue (by norm_num) (by norm_num) (by norm_num),
    div_eq_one_of_eValueLimit (by norm_num)⟩
  rw [eValueLimit, ite_eq_left (by norm_num : (1 : ℝ) < 2), eValue_two]

/-- **A confounder below the E-value of the limit leaves the lower limit above the null.** For
the interval `(2, 3)` and the pair `(2, 3)`, `max 2 3 = 3 < 2 + √2`, so `2 / B > 1` for every
bias `0 < B ≤ boundingFactor 2 3`. -/
theorem one_lt_div_instance {B : ℝ} (hB0 : 0 < B) (hB : B ≤ boundingFactor 2 3) :
    1 < 2 / B := by
  refine one_lt_div_of_max_lt_eValueLimit (hi := 3) (by norm_num) (by norm_num) (by norm_num) ?_
    hB0 hB
  rw [eValueLimit, ite_eq_left (by norm_num : (1 : ℝ) < 2), eValue_two]
  have : (1 : ℝ) < Real.sqrt 2 := by
    rw [Real.lt_sqrt zero_le_one]; norm_num
  norm_num
  linarith

end IndirectComparisonBias

end BiasAnalysis

end CausalInference
