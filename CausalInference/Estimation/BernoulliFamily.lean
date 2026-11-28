/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.Estimation.CramerRao

/-!
# The Bernoulli family

The Bernoulli family on `{false, true}` with counting measure, parameter set `Θ = (0, 1)` and
density `f(x;p) = p` for a success and `1 - p` for a failure. Every hypothesis of the score,
information and Cramér-Rao theorems is discharged here: the family is regular at every
`p ∈ (0, 1)`, its information is `I(p) = 1 / (p (1 - p))`, the success indicator attains the
Cramér-Rao bound and is efficient, and the sample mean of `n` observations attains the bound
`1 / (n I(p)) = p (1 - p) / n` of the sample family.

## Main definitions

* `CausalInference.ParametricFamily.bernoulli`: the family.
* `CausalInference.ParametricFamily.successIndicator`: `T(x) = 1` for a success, `0` otherwise.
* `CausalInference.ParametricFamily.bernoulliSampleMean`: the sample proportion of `n`
  observations.

## Main results

* `CausalInference.ParametricFamily.bernoulli_fisherInfo`: `I(p) = 1 / (p (1 - p))`.
* `CausalInference.ParametricFamily.bernoulli_isRegularAt`: regularity at every `p ∈ (0, 1)`.
* `CausalInference.ParametricFamily.bernoulli_cramer_rao_attained` and
  `bernoulli_isEfficient`: the success indicator attains the bound and is efficient.
* `CausalInference.ParametricFamily.bernoulli_pi_cramer_rao_attained`: the sample proportion
  attains the bound for a sample of size `n`.

References: E. L. Lehmann and G. Casella (1998), *Theory of Point Estimation*, 2nd edition,
chapter 2.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology Metric
open scoped ENNReal

namespace CausalInference

namespace ParametricFamily

/-- The Bernoulli family: counting measure on `Bool`, `Θ = (0, 1)`, `f(x;p) = p` for
`x = true` and `1 - p` for `x = false`. -/
noncomputable def bernoulli : ParametricFamily ℝ Bool where
  ν := Measure.count
  Θ := Set.Ioo 0 1
  density p x := if x then p else 1 - p
  measurable_density _ := .of_discrete
  density_nonneg p hp x := by
    cases x
    · simp only [Bool.false_eq_true, ↓reduceIte, sub_nonneg]; exact hp.2.le
    · simp only [↓reduceIte]; exact hp.1.le
  integrable_density _ _ := Integrable.of_finite
  integral_density p _ := by simp

/-- The counting measure on `Bool` is finite. -/
instance : IsFiniteMeasure bernoulli.ν :=
  inferInstanceAs (IsFiniteMeasure (Measure.count : Measure Bool))

/-- The product of counting measures on `Fin n → Bool` is finite. -/
instance (n : ℕ) : IsFiniteMeasure (bernoulli.pi n).ν :=
  inferInstanceAs (IsFiniteMeasure (Measure.pi fun _ : Fin n ↦ (Measure.count : Measure Bool)))

/-- The indicator of a success. -/
def successIndicator (x : Bool) : ℝ := if x then 1 else 0

/-- The Bernoulli density at `x`. -/
theorem bernoulli_density (p : ℝ) (x : Bool) :
    bernoulli.density p x = if x then p else 1 - p := rfl

/-- Expectation under the Bernoulli law: `E_p[h] = p h(true) + (1 - p) h(false)`. -/
theorem bernoulli_integral_law {p : ℝ} (hp : p ∈ Set.Ioo (0 : ℝ) 1) (h : Bool → ℝ) :
    ∫ x, h x ∂bernoulli.law p = p * h true + (1 - p) * h false := by
  rw [integral_law hp]
  simp [bernoulli]

/-- The derivative of the Bernoulli density in `p`: `1` at a success, `-1` at a failure. -/
theorem bernoulli_densityDeriv (p : ℝ) (x : Bool) :
    bernoulli.densityDeriv p x = if x then 1 else -1 := by
  cases x <;> simp [densityDeriv, bernoulli]

/-- The second derivative of the Bernoulli density in `p` vanishes. -/
theorem bernoulli_densityDeriv2 (p : ℝ) (x : Bool) : bernoulli.densityDeriv2 p x = 0 := by
  have : (fun v ↦ bernoulli.densityDeriv v x) = fun _ ↦ if x then (1 : ℝ) else -1 :=
    funext fun v ↦ bernoulli_densityDeriv v x
  rw [densityDeriv2, this, deriv_const]

/-- **The Bernoulli information** `I(p) = 1 / (p (1 - p))`. -/
theorem bernoulli_fisherInfo {p : ℝ} (hp : p ∈ Set.Ioo (0 : ℝ) 1) :
    bernoulli.fisherInfo p = 1 / (p * (1 - p)) := by
  have h1 : 1 - p ≠ 0 := by linarith [hp.2]
  have h0 : p ≠ 0 := hp.1.ne'
  rw [fisherInfo, bernoulli_integral_law hp]
  simp only [score, bernoulli_densityDeriv]
  simp [bernoulli]
  field_simp
  ring

/-- The Bernoulli information is positive on `(0, 1)`. -/
theorem bernoulli_fisherInfo_pos {p : ℝ} (hp : p ∈ Set.Ioo (0 : ℝ) 1) :
    0 < bernoulli.fisherInfo p := by
  rw [bernoulli_fisherInfo hp]
  exact one_div_pos.2 (mul_pos hp.1 (by linarith [hp.2]))

/-- The success indicator is unbiased for `p`: `E_p[T] = p`. -/
theorem bernoulli_mean {p : ℝ} (hp : p ∈ Set.Ioo (0 : ℝ) 1) :
    bernoulli.mean successIndicator p = p := by
  rw [mean, bernoulli_integral_law hp]
  simp [successIndicator]

/-- The success indicator is an unbiased estimator of `p`. -/
theorem bernoulli_isUnbiased : bernoulli.IsUnbiased successIndicator id := fun _ hp ↦
  have := isProbabilityMeasure_law (F := bernoulli) hp
  ⟨Integrable.of_finite, bernoulli_mean hp⟩

/-- The variance of the success indicator is `p (1 - p)`. -/
theorem bernoulli_variance {p : ℝ} (hp : p ∈ Set.Ioo (0 : ℝ) 1) :
    Var[successIndicator; bernoulli.law p] = p * (1 - p) := by
  have := isProbabilityMeasure_law (F := bernoulli) hp
  rw [variance_eq_integral (Measurable.of_discrete).aemeasurable, bernoulli_integral_law hp,
    ← mean, bernoulli_mean hp]
  simp [successIndicator]
  ring

/-- The Bernoulli densities are positive on `(0, 1)`. -/
theorem bernoulli_density_pos {p : ℝ} (hp : p ∈ Set.Ioo (0 : ℝ) 1) (x : Bool) :
    0 < bernoulli.density p x := by
  cases x
  · change 0 < (if false = true then p else 1 - p); simp; linarith [hp.2]
  · change 0 < (if true = true then p else 1 - p); simpa using hp.1

/-- The ball of radius `min p (1 - p)` around `p ∈ (0, 1)` lies in `(0, 1)`. -/
theorem ball_subset_Ioo (p : ℝ) :
    ball p (min p (1 - p)) ⊆ Set.Ioo 0 1 := by
  intro u hu
  rw [mem_ball, Real.dist_eq, abs_lt] at hu
  constructor <;> linarith [min_le_left p (1 - p), min_le_right p (1 - p), hu.1, hu.2]

/-- **The Bernoulli family is regular** at every `p ∈ (0, 1)`: the support is all of `Bool`, the
density is affine in `p` (envelopes `1` and `0`), and the score is bounded. -/
theorem bernoulli_isRegularAt {p : ℝ} (hp : p ∈ Set.Ioo (0 : ℝ) 1) :
    bernoulli.IsRegularAt p := by
  have := isProbabilityMeasure_law (F := bernoulli) hp
  refine ⟨?_, ⟨min p (1 - p), lt_min hp.1 (by linarith [hp.2]), ball_subset_Ioo p, ?_,
    fun _ ↦ 1, fun _ ↦ 0, integrable_const (μ := (Measure.count : Measure Bool)) (1 : ℝ),
    integrable_const (μ := (Measure.count : Measure Bool)) (0 : ℝ), ?_⟩, MemLp.of_discrete⟩
  · filter_upwards [isOpen_Ioo.mem_nhds hp] with u hu x
    exact iff_of_true (bernoulli_density_pos hu x) (bernoulli_density_pos hp x)
  · refine Eventually.of_forall fun x ↦ ?_
    cases x
    · exact (contDiff_const.sub contDiff_id).contDiffOn
    · exact contDiff_id.contDiffOn
  · refine Eventually.of_forall fun x u _ ↦ ⟨?_, by simp [bernoulli_densityDeriv2]⟩
    rw [bernoulli_densityDeriv]
    cases x <;> simp

/-- **The success indicator attains the Cramér-Rao bound.** At every `p ∈ (0, 1)`, the bound
`1 / I(p) ≤ Var_p(T)` holds (by `IsRegularAt.cramer_rao_of_bounded`, with no interchange
hypothesis), `I(p) = 1 / (p (1 - p))`, and `Var_p(T) = p (1 - p) = 1 / I(p)`. -/
theorem bernoulli_cramer_rao_attained {p : ℝ} (hp : p ∈ Set.Ioo (0 : ℝ) 1) :
    bernoulli.fisherInfo p = 1 / (p * (1 - p)) ∧
      1 / bernoulli.fisherInfo p ≤ Var[successIndicator; bernoulli.law p] ∧
      Var[successIndicator; bernoulli.law p] = 1 / bernoulli.fisherInfo p := by
  have hd : deriv (bernoulli.mean successIndicator) p = 1 := by
    simpa using deriv_mean_of_isUnbiased (isOpen_Ioo.mem_nhds hp) bernoulli_isUnbiased
      (hasDerivAt_id p)
  have hb := ((bernoulli_isRegularAt hp).cramer_rao_of_bounded (bernoulli_fisherInfo_pos hp)
    (T := successIndicator) .of_discrete (C := 1)
    (fun x ↦ by cases x <;> simp [successIndicator])).1
  rw [hd, one_pow] at hb
  refine ⟨bernoulli_fisherInfo hp, hb, ?_⟩
  rw [bernoulli_variance hp, bernoulli_fisherInfo hp, one_div_one_div]

/-- **The success indicator is an efficient estimator of `p`.** -/
theorem bernoulli_isEfficient : bernoulli.IsEfficient successIndicator id := by
  refine ⟨bernoulli_isUnbiased, fun p hp ↦ ?_⟩
  have := isProbabilityMeasure_law (F := bernoulli) hp
  refine ⟨MemLp.of_discrete, bernoulli_fisherInfo_pos hp, ?_⟩
  rw [deriv_id, one_pow]
  exact (bernoulli_cramer_rao_attained hp).2.2

/-! ### A sample of size `n` -/

/-- The sample proportion `n⁻¹ ∑_i T(x_i)` of `n` Bernoulli observations. -/
noncomputable def bernoulliSampleMean (n : ℕ) (x : Fin n → Bool) : ℝ :=
  (n : ℝ)⁻¹ * ∑ i, successIndicator (x i)

/-- The likelihood of `n` Bernoulli observations has derivative
`∑_i (∏_{j ≠ i} f(x_j;u)) ∂_u f(x_i;u)` in the parameter. -/
theorem bernoulli_pi_hasDerivAt (n : ℕ) (x : Fin n → Bool) (u : ℝ) :
    HasDerivAt (fun v ↦ (bernoulli.pi n).density v x)
      (∑ i, (∏ j ∈ Finset.univ.erase i, bernoulli.density u (x j)) *
        (if x i then 1 else -1)) u := by
  have hd : ∀ i, HasDerivAt (fun v ↦ bernoulli.density v (x i)) (if x i then 1 else -1) u :=
    fun i ↦ by
      cases x i
      · simpa [bernoulli_density] using (hasDerivAt_id u).const_sub 1
      · simpa [bernoulli_density] using hasDerivAt_id' u
  have := HasDerivAt.fun_finsetProd (u := Finset.univ)
    (f := fun i v ↦ bernoulli.density v (x i)) (fun i _ ↦ hd i)
  simp only [smul_eq_mul] at this
  exact this

/-- On `(0, 1)` the derivative of the likelihood of `n` Bernoulli observations is at most `n` in
absolute value. -/
theorem abs_bernoulli_pi_densityDeriv_le (n : ℕ) (x : Fin n → Bool) {u : ℝ}
    (hu : u ∈ Set.Ioo (0 : ℝ) 1) : |(bernoulli.pi n).densityDeriv u x| ≤ (n : ℝ) := by
  rw [densityDeriv, (bernoulli_pi_hasDerivAt n x u).deriv]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  have hle : ∀ i, |(∏ j ∈ Finset.univ.erase i, bernoulli.density u (x j)) *
      (if x i then 1 else -1)| ≤ 1 := fun i ↦ by
    have h0 : ∀ j, 0 ≤ bernoulli.density u (x j) := fun j ↦ (bernoulli_density_pos hu _).le
    have h1 : ∀ j, bernoulli.density u (x j) ≤ 1 := fun j ↦ by
      rw [bernoulli_density]; split_ifs <;> linarith [hu.1, hu.2]
    rw [abs_mul, abs_of_nonneg (Finset.prod_nonneg fun j _ ↦ h0 j)]
    have hs : |(if x i then (1 : ℝ) else -1)| = 1 := by split_ifs <;> simp
    rw [hs, mul_one]
    exact Finset.prod_le_one₀ (fun j _ ↦ h0 j) fun j _ ↦ h1 j
  calc ∑ i, |(∏ j ∈ Finset.univ.erase i, bernoulli.density u (x j)) *
        (if x i then 1 else -1)| ≤ ∑ _i : Fin n, (1 : ℝ) := Finset.sum_le_sum fun i _ ↦ hle i
    _ = n := by simp

/-- The sample proportion is measurable. -/
theorem measurable_bernoulliSampleMean (n : ℕ) : Measurable (bernoulliSampleMean n) := by
  unfold bernoulliSampleMean
  exact measurable_const.mul (Finset.measurable_sum _ fun i _ ↦
    (Measurable.of_discrete (f := successIndicator)).comp (measurable_pi_apply i))

/-- Under `n` i.i.d. Bernoulli observations with parameter `u`, the success indicator of each
observation has mean `u` and variance `u (1 - u)`. -/
theorem bernoulli_pi_coord {n : ℕ} {u : ℝ} (hu : u ∈ Set.Ioo (0 : ℝ) 1) (i : Fin n) :
    ∫ x, successIndicator (x i) ∂(Measure.pi fun _ ↦ bernoulli.law u) = u ∧
      Var[fun x : Fin n → Bool ↦ successIndicator (x i); Measure.pi fun _ ↦ bernoulli.law u] =
        u * (1 - u) := by
  have := isProbabilityMeasure_law (F := bernoulli) hu
  have hmp := measurePreserving_eval (fun _ : Fin n ↦ bernoulli.law u) i
  constructor
  · have h := integral_map (μ := Measure.pi fun _ : Fin n ↦ bernoulli.law u)
      (measurable_pi_apply i).aemeasurable
      (Measurable.of_discrete (f := successIndicator)).aestronglyMeasurable
    rw [hmp.map_eq] at h
    rw [← h]
    exact bernoulli_mean hu
  · have h := variance_map (μ := Measure.pi fun _ : Fin n ↦ bernoulli.law u)
      (Measurable.of_discrete (f := successIndicator)).aemeasurable
      (measurable_pi_apply i).aemeasurable
    rw [hmp.map_eq] at h
    rw [← bernoulli_variance hu, h]
    rfl

/-- The sample proportion is unbiased for `p` under `n ≥ 1` i.i.d. observations. -/
theorem bernoulli_pi_isUnbiased {n : ℕ} (hn : 0 < n) :
    (bernoulli.pi n).IsUnbiased (bernoulliSampleMean n) id := by
  intro u hu
  have := isProbabilityMeasure_law (F := bernoulli) hu
  rw [pi_law (F := bernoulli) n hu]
  refine ⟨Integrable.of_finite, ?_⟩
  rw [mean, pi_law (F := bernoulli) n hu]
  unfold bernoulliSampleMean
  rw [integral_const_mul,
    integral_finsetSum _ fun i _ ↦ Integrable.of_finite]
  simp only [fun i ↦ (bernoulli_pi_coord (n := n) hu i).1]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, id]
  field_simp

/-- The variance of the sample proportion is `p (1 - p) / n`. -/
theorem bernoulli_pi_variance {n : ℕ} {p : ℝ} (hp : p ∈ Set.Ioo (0 : ℝ) 1) :
    Var[bernoulliSampleMean n; Measure.pi fun _ ↦ bernoulli.law p] = p * (1 - p) / n := by
  have := isProbabilityMeasure_law (F := bernoulli) hp
  have hind : iIndepFun (fun i (x : Fin n → Bool) ↦ x i) (Measure.pi fun _ ↦ bernoulli.law p) :=
    iIndepFun_pi (X := fun _ ↦ id) fun _ ↦ aemeasurable_id
  have hY : ∀ i, MemLp (fun x : Fin n → Bool ↦ successIndicator (x i)) 2
      (Measure.pi fun _ ↦ bernoulli.law p) := fun _ ↦ MemLp.of_discrete
  have hfun : bernoulliSampleMean n =
      fun x ↦ (n : ℝ)⁻¹ * (∑ i, fun x : Fin n → Bool ↦ successIndicator (x i)) x := by
    ext x; simp [bernoulliSampleMean]
  rw [hfun, variance_const_mul, IndepFun.variance_sum (fun i _ ↦ hY i)]
  · simp only [fun i ↦ (bernoulli_pi_coord (n := n) hp i).2, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn; simp
    · have : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hn.ne'
      field_simp
  · intro i _ j _ hij
    exact (hind.indepFun hij).comp (Measurable.of_discrete (f := successIndicator))
      (Measurable.of_discrete (f := successIndicator))

/-- **The sample proportion attains the Cramér-Rao bound for a sample of size `n ≥ 1`.** The
sample family has information `n I(p) = n / (p (1 - p))`, the bound `1 / (n I(p))` holds (by
`cramer_rao_pi`, every hypothesis discharged), and the variance of the sample proportion is
`p (1 - p) / n = 1 / (n I(p))`. -/
theorem bernoulli_pi_cramer_rao_attained {n : ℕ} (hn : 0 < n) {p : ℝ}
    (hp : p ∈ Set.Ioo (0 : ℝ) 1) :
    (bernoulli.pi n).fisherInfo p = n * (1 / (p * (1 - p))) ∧
      1 / (n * bernoulli.fisherInfo p) ≤
        Var[bernoulliSampleMean n; Measure.pi fun _ ↦ bernoulli.law p] ∧
      Var[bernoulliSampleMean n; Measure.pi fun _ ↦ bernoulli.law p] =
        1 / (n * bernoulli.fisherInfo p) := by
  have hΘ : bernoulli.Θ ∈ 𝓝 p := isOpen_Ioo.mem_nhds hp
  have hreg := bernoulli_isRegularAt hp
  have hε : 0 < min p (1 - p) := lt_min hp.1 (by linarith [hp.2])
  have hT : (bernoulli.pi n).MeanDerivInterchange (bernoulliSampleMean n) p := by
    refine meanDerivInterchange_of_bounded (measurable_bernoulliSampleMean n) (C := 1) ?_ hε
      (ball_subset_Ioo p) (b := fun _ ↦ (n : ℝ)) (integrable_const _)
      (ae_of_all _ fun x u _ ↦ (bernoulli_pi_hasDerivAt n x u).differentiableAt)
      (ae_of_all _ fun x u hu ↦ abs_bernoulli_pi_densityDeriv_le n x (ball_subset_Ioo p hu))
    intro x
    have h0 : 0 ≤ ∑ i, successIndicator (x i) :=
      Finset.sum_nonneg fun i _ ↦ by unfold successIndicator; split_ifs <;> norm_num
    have h1 : ∑ i, successIndicator (x i) ≤ n := by
      calc ∑ i, successIndicator (x i) ≤ ∑ _i : Fin n, (1 : ℝ) :=
            Finset.sum_le_sum fun i _ ↦ by unfold successIndicator; split_ifs <;> norm_num
        _ = n := by simp
    have hn' : (0 : ℝ) < n := Nat.cast_pos.2 hn
    rw [bernoulliSampleMean, abs_of_nonneg (mul_nonneg (inv_nonneg.2 hn'.le) h0)]
    calc (n : ℝ)⁻¹ * ∑ i, successIndicator (x i) ≤ (n : ℝ)⁻¹ * n :=
          mul_le_mul_of_nonneg_left h1 (inv_nonneg.2 hn'.le)
      _ = 1 := inv_mul_cancel₀ hn'.ne'
  have hd : deriv ((bernoulli.pi n).mean (bernoulliSampleMean n)) p = 1 := by
    simpa using deriv_mean_of_isUnbiased (F := bernoulli.pi n) hΘ (bernoulli_pi_isUnbiased hn)
      (hasDerivAt_id p)
  have := isProbabilityMeasure_law (F := bernoulli) hp
  have hb := cramer_rao_pi hn hΘ hreg.derivInterchange.self_of_nhds hreg.ae_differentiableAt hT
    MemLp.of_discrete hreg.memLp_score (bernoulli_fisherInfo_pos hp)
  rw [hd, one_pow] at hb
  refine ⟨?_, hb, ?_⟩
  · rw [(pi_fisherInfo n hΘ hreg.derivInterchange.self_of_nhds hreg.ae_differentiableAt
      hreg.memLp_score).2, bernoulli_fisherInfo hp]
  · rw [bernoulli_pi_variance hp, bernoulli_fisherInfo hp]
    have h1 : 1 - p ≠ 0 := by linarith [hp.2]
    have h0 : p ≠ 0 := hp.1.ne'
    have : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hn.ne'
    field_simp

end ParametricFamily

end CausalInference
