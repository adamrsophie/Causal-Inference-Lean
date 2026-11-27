/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.Estimation.DeltaMethod
public import Mathlib.Analysis.Calculus.FDeriv.Pi
public import Mathlib.Analysis.Calculus.Deriv.Pi
public import Mathlib.Probability.Independence.Integration

/-!
# The multivariate delta method for asymptotically linear estimators

Let `θhat i` (`i` in a finite index type) be estimators that are asymptotically linear at `θ i`
with influence functions `φ i` for one i.i.d. sample `O`, and let `g : (ι → ℝ) → ℝ` be
(Fréchet) differentiable at the vector `θ` with derivative `L`. Then `g` of the vector of
estimators is asymptotically linear at `g θ` with influence function
`x ↦ ∑ i, L (eᵢ) φ i x`, where `L (eᵢ)` is the `i`th partial derivative. Its asymptotic variance
is the quadratic form `∑ i, ∑ j, cᵢ cⱼ E[φ i (O) φ j (O)]` of the gradient `c` in the covariance
matrix of the influence functions; when the influence functions are pairwise independent at the
observation, it is `∑ i, cᵢ² E[φ i (O)²]`.

Main results:

* `IsAsymptoticallyLinear.const`, `.const_add`, `.finset_sum`, `.sum_const_mul`: constants and
  finite linear combinations of asymptotically linear estimators.
* `tendstoInMeasure_pi_comp`: the continuous mapping theorem for a finite vector of sequences
  converging in probability, and `boundedInProbability_norm_pi`: a vector whose coordinates are
  bounded in probability has a sup norm bounded in probability.
* `IsAsymptoticallyLinear.comp_hasFDerivAt`: **the multivariate delta method**, and
  `IsAsymptoticallyLinear.comp_of_partials`: the same with the derivative given by partial
  derivatives (`HasDerivAt` along each coordinate) at a point of differentiability.
* `integral_sq_sum_mul`, `IsAsymptoticallyLinear.integral_sq_eq_sum_cov`: the asymptotic
  variance is the quadratic form of the gradient in the covariance matrix of the influence
  functions; `IsAsymptoticallyLinear.integral_sq_of_indep`: for pairwise independent influence
  functions it is the sum of squared partial derivatives times variances.
* `IsAsymptoticallyLinear.tendstoInDistribution_comp_hasFDerivAt`: asymptotic normality,
  `√n (g (θhat n) - g θ) ⇒ N(0, ∑ i, ∑ j, cᵢ cⱼ E[φ i φ j])`.
* `IsAsymptoticallyLinear.twoSample_integral_sq`: two independent samples observed in pairs.

## Where independence enters, and samples of different sizes

The sample model of the library has one i.i.d. sequence of observations `O k` and one sample
size `n`. Several estimates computed from independent studies (two binomial groups, a validation
study and a main study) fit this model when each observation is a tuple with one independent
component per study, `O k = (A k, B k)`, and the influence function of each estimate depends only
on its own component. Independence of the components at one observation then makes the cross
moments `E[φ i (O) φ j (O)]` vanish (`integral_sq_of_indep`, `twoSample_integral_sq`), and only
there. This covers studies of the same size `n`. Studies of different sizes `n₁ = a n`,
`n₂ = b n` with a fixed ratio are not covered: they need the estimate of a study of size `a n`
to be asymptotically linear in the sample of blocks `(A (a k), …, A (a k + a - 1))`, which holds
with influence function `a⁻¹ ∑_l φ (A_l)` along the subsequence `a n`, and an i.i.d. property of
the joint blocks of the two studies; neither step is formalized here. In that case the asymptotic
variance per block is `∑ᵢ cᵢ² σᵢ² / rᵢ`, with `rᵢ` the block length of study `i`, which is the
printed form `∑ᵢ cᵢ² σᵢ² / nᵢ` after division by `n`.

Source: A. W. van der Vaart (1998), *Asymptotic Statistics*, chapter 3 (Theorem 3.1 in the
asymptotically linear form).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Finset
open scoped Topology ENNReal NNReal

namespace CausalInference

variable {Ω 𝒪 : Type*} {mΩ : MeasurableSpace Ω} [MeasurableSpace 𝒪]

/-! ### Linear combinations of asymptotically linear estimators -/

namespace IsAsymptoticallyLinear

variable {μ : Measure Ω} {O : ℕ → Ω → 𝒪}

/-- A constant estimator `a` is asymptotically linear at `a` with influence function zero. -/
theorem const (μ : Measure Ω) [IsProbabilityMeasure μ] (O : ℕ → Ω → 𝒪) (a : ℝ) :
    IsAsymptoticallyLinear (fun _ _ ↦ a) a (fun _ ↦ 0) O μ where
  measurable := measurable_const
  memLp := memLp_const 0
  integral_eq_zero := by simp
  remainder := by
    have h0 : (fun (n : ℕ) (_ : Ω) ↦ √n * (a - a) - (√n)⁻¹ * ∑ i ∈ range n, (0 : ℝ)) =
        fun _ _ ↦ 0 := by
      funext n ω
      simp
    rw [h0, tendstoInMeasure_iff_norm]
    intro ε hε
    simp [not_le.2 hε]

/-- Adding a constant `a` to an asymptotically linear estimator shifts its limit by `a` and keeps
its influence function. -/
theorem const_add [IsProbabilityMeasure μ] {θhat : ℕ → Ω → ℝ} {θ : ℝ} {φ : 𝒪 → ℝ} (a : ℝ)
    (h : IsAsymptoticallyLinear θhat θ φ O μ) :
    IsAsymptoticallyLinear (fun n ω ↦ a + θhat n ω) (a + θ) φ O μ := by
  have h' := (const μ O a).add h
  simp only [zero_add] at h'
  exact h'

/-- **Finite sums.** If `θhat i` is asymptotically linear at `θ i` with influence function `φ i`
for every `i ∈ s`, then `∑ i ∈ s, θhat i` is asymptotically linear at `∑ i ∈ s, θ i` with
influence function `∑ i ∈ s, φ i`. -/
theorem finset_sum [IsProbabilityMeasure μ] {ι : Type*} (s : Finset ι) {θhat : ι → ℕ → Ω → ℝ}
    {θ : ι → ℝ} {φ : ι → 𝒪 → ℝ} (h : ∀ i ∈ s, IsAsymptoticallyLinear (θhat i) (θ i) (φ i) O μ) :
    IsAsymptoticallyLinear (fun n ω ↦ ∑ i ∈ s, θhat i n ω) (∑ i ∈ s, θ i)
      (fun x ↦ ∑ i ∈ s, φ i x) O μ := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using const μ O 0
  | insert j s hj ih =>
    have h1 := (h j (mem_insert_self j s)).add (ih fun i hi ↦ h i (mem_insert_of_mem hi))
    simpa [sum_insert hj] using h1

/-- **Linear combinations.** `∑ i ∈ s, cᵢ θhat i` is asymptotically linear at `∑ i ∈ s, cᵢ θ i`
with influence function `∑ i ∈ s, cᵢ φ i`. -/
theorem sum_const_mul [IsProbabilityMeasure μ] {ι : Type*} (s : Finset ι) (c : ι → ℝ)
    {θhat : ι → ℕ → Ω → ℝ} {θ : ι → ℝ} {φ : ι → 𝒪 → ℝ}
    (h : ∀ i ∈ s, IsAsymptoticallyLinear (θhat i) (θ i) (φ i) O μ) :
    IsAsymptoticallyLinear (fun n ω ↦ ∑ i ∈ s, c i * θhat i n ω) (∑ i ∈ s, c i * θ i)
      (fun x ↦ ∑ i ∈ s, c i * φ i x) O μ :=
  finset_sum s fun i hi ↦ (h i hi).const_mul (c i)

end IsAsymptoticallyLinear

/-! ### Vectors of sequences converging in probability -/

/-- **Continuous mapping for a finite vector.** If `X i n → θ i` in probability for every
coordinate `i` of a finite index type and `ρ` is continuous at the vector `θ`, then
`ρ (X · n) → ρ θ` in probability. -/
theorem tendstoInMeasure_pi_comp {ι : Type*} [Finite ι] {μ : Measure Ω}
    {X : ι → ℕ → Ω → ℝ} {θ : ι → ℝ} (hX : ∀ i, TendstoInMeasure μ (X i) atTop (fun _ ↦ θ i))
    {ρ : (ι → ℝ) → ℝ} (hρ : ContinuousAt ρ θ) :
    TendstoInMeasure μ (fun n ω ↦ ρ (fun i ↦ X i n ω)) atTop (fun _ ↦ ρ θ) := by
  have := Fintype.ofFinite ι
  simp only [tendstoInMeasure_iff_norm] at hX ⊢
  intro ε hε
  obtain ⟨δ, hδ, hball⟩ := Metric.continuousAt_iff.1 hρ ε hε
  have hsum : Tendsto (fun n ↦ ∑ i, μ {ω | δ ≤ ‖X i n ω - θ i‖}) atTop (𝓝 0) := by
    simpa using tendsto_finsetSum univ fun i _ ↦ hX i δ hδ
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsum (fun n ↦ bot_le)
    fun n ↦ (measure_mono ?_).trans (measure_iUnion_fintype_le μ _)
  intro ω hω
  simp only [Set.mem_ofPred_eq, Set.mem_iUnion] at hω ⊢
  by_contra! hlt
  have hd : dist (fun i ↦ X i n ω) θ < δ := by
    rw [dist_pi_lt_iff hδ]
    intro i
    rw [Real.dist_eq]
    simpa [Real.norm_eq_abs] using hlt i
  have h1 := hball hd
  rw [Real.dist_eq] at h1
  rw [Real.norm_eq_abs] at hω
  linarith

/-- **Bounded in probability, vector form.** If every coordinate `Y i n` of a finite vector is
bounded in probability, so is its sup norm. -/
theorem boundedInProbability_norm_pi {ι : Type*} [Fintype ι] {μ : Measure Ω}
    {Y : ι → ℕ → Ω → ℝ}
    (hY : ∀ i, ∀ η : ℝ≥0∞, 0 < η → ∃ M : ℝ, 0 < M ∧ ∀ᶠ n in atTop, μ {ω | M ≤ |Y i n ω|} ≤ η) :
    ∀ η : ℝ≥0∞, 0 < η →
      ∃ M : ℝ, 0 < M ∧ ∀ᶠ n in atTop, μ {ω | M ≤ |‖fun i ↦ Y i n ω‖|} ≤ η := by
  intro η hη
  have hη' : 0 < η / (Fintype.card ι : ℝ≥0∞) :=
    ENNReal.div_pos hη.ne' (ENNReal.natCast_ne_top _)
  choose M hM hev using fun i ↦ hY i _ hη'
  have hMs : 0 ≤ ∑ i, M i := sum_nonneg fun i _ ↦ (hM i).le
  refine ⟨1 + ∑ i, M i, by linarith, ?_⟩
  filter_upwards [eventually_all.2 hev] with n hn
  calc μ {ω | 1 + ∑ i, M i ≤ |‖fun i ↦ Y i n ω‖|}
      ≤ μ (⋃ i, {ω | M i ≤ |Y i n ω|}) := measure_mono ?_
    _ ≤ ∑ i, μ {ω | M i ≤ |Y i n ω|} := measure_iUnion_fintype_le μ _
    _ ≤ ∑ _i : ι, η / (Fintype.card ι : ℝ≥0∞) := sum_le_sum fun i _ ↦ hn i
    _ = (Fintype.card ι : ℝ≥0∞) * (η / (Fintype.card ι : ℝ≥0∞)) := by
      rw [sum_const, card_univ, nsmul_eq_mul]
    _ ≤ η := ENNReal.mul_div_le
  intro ω hω
  simp only [Set.mem_ofPred_eq, Set.mem_iUnion] at hω ⊢
  by_contra! hlt
  have hlt' : ‖fun i ↦ Y i n ω‖ < 1 + ∑ i, M i := by
    rw [pi_norm_lt_iff (by linarith)]
    intro i
    rw [Real.norm_eq_abs]
    calc |Y i n ω| < M i := hlt i
      _ ≤ ∑ j, M j := single_le_sum (fun j _ ↦ (hM j).le) (mem_univ i)
      _ ≤ 1 + ∑ j, M j := by linarith
  rw [abs_of_nonneg (norm_nonneg _)] at hω
  linarith

/-- A continuous linear functional on `ι → ℝ` is the sum of its values on the unit vectors times
the coordinates: `L v = ∑ i, L (eᵢ) vᵢ`. -/
theorem clm_apply_eq_sum_single {ι : Type*} [Fintype ι] [DecidableEq ι]
    (L : (ι → ℝ) →L[ℝ] ℝ) (v : ι → ℝ) : L v = ∑ i, L (Pi.single i 1) * v i := by
  have h := LinearMap.pi_apply_eq_sum_univ L.toLinearMap v
  simp only [ContinuousLinearMap.coe_coe, smul_eq_mul] at h
  rw [h]
  refine sum_congr rfl fun i _ ↦ ?_
  rw [mul_comm]
  congr 2
  funext j
  simp [Pi.single_apply, eq_comm]

/-! ### The multivariate delta method -/

namespace IsAsymptoticallyLinear

variable {μ : Measure Ω} {O : ℕ → Ω → 𝒪}

/-- **The multivariate delta method.** Let `θhat i` be asymptotically linear at `θ i` with
influence function `φ i`, for every `i` of a finite index type, all for the same i.i.d. sample
`O` under a probability measure `μ`, and let `g : (ι → ℝ) → ℝ` have Fréchet derivative `L` at
the vector `θ`. Then `g (θhat · n)` is asymptotically linear at `g θ` with influence function
`x ↦ ∑ i, L (eᵢ) φ i x`. The proof writes `g x - g θ - L (x - θ) = ρ x ‖x - θ‖` with `ρ`
continuous at `θ` and `ρ θ = 0`; `ρ (θhat n) → 0` in probability by consistency of each
coordinate and `√n ‖θhat n - θ‖` is bounded in probability. -/
theorem comp_hasFDerivAt {ι : Type*} [Fintype ι] [DecidableEq ι] [IsProbabilityMeasure μ]
    (hO : IsIIDSample O μ) {θhat : ι → ℕ → Ω → ℝ} {θ : ι → ℝ} {φ : ι → 𝒪 → ℝ}
    (h : ∀ i, IsAsymptoticallyLinear (θhat i) (θ i) (φ i) O μ)
    {g : (ι → ℝ) → ℝ} {L : (ι → ℝ) →L[ℝ] ℝ} (hg : HasFDerivAt g L θ) :
    IsAsymptoticallyLinear (fun n ω ↦ g (fun i ↦ θhat i n ω)) (g θ)
      (fun x ↦ ∑ i, L (Pi.single i 1) * φ i x) O μ := by
  set c : ι → ℝ := fun i ↦ L (Pi.single i 1) with hc
  have hlin := const_add (g θ - ∑ i, c i * θ i) (sum_const_mul univ c fun i _ ↦ h i)
  rw [sub_add_cancel] at hlin
  refine hlin.of_tendstoInMeasure_sqrt_mul_sub ?_
  set ρ : (ι → ℝ) → ℝ := fun x ↦ (g x - g θ - L (x - θ)) / ‖x - θ‖ with hρ
  have hkey : ∀ x, g x - g θ - L (x - θ) = ρ x * ‖x - θ‖ := by
    intro x
    by_cases hx : x = θ
    · subst hx
      simp
    · have hn : ‖x - θ‖ ≠ 0 := norm_ne_zero_iff.2 (sub_ne_zero.2 hx)
      simp only [hρ]
      field_simp
  have hρθ : ρ θ = 0 := by simp [hρ]
  have hρc : ContinuousAt ρ θ := by
    rw [ContinuousAt, hρθ, tendsto_zero_iff_norm_tendsto_zero]
    refine (hasFDerivAt_iff_tendsto.1 hg).congr fun x ↦ ?_
    simp only [hρ, norm_div, norm_norm]
    ring
  clear_value ρ
  have hcons : TendstoInMeasure μ (fun n ω ↦ ρ (fun i ↦ θhat i n ω)) atTop 0 := by
    have := tendstoInMeasure_pi_comp (fun i ↦ (h i).isConsistent hO) hρc
    rw [hρθ] at this
    exact this
  have hbdd := boundedInProbability_norm_pi (μ := μ)
    (Y := fun i (n : ℕ) ω ↦ √n * (θhat i n ω - θ i))
    fun i ↦ (h i).sqrt_mul_sub_boundedInProbability hO
  refine (tendstoInMeasure_mul_of_bounded hcons hbdd).congr'
    (Eventually.of_forall fun n ↦ Eventually.of_forall fun ω ↦ ?_) EventuallyEq.rfl
  set x : ι → ℝ := fun i ↦ θhat i n ω with hx
  have hL : L (x - θ) = ∑ i, c i * (θhat i n ω - θ i) := by
    rw [clm_apply_eq_sum_single L]
    rfl
  have hnorm : ‖fun i ↦ √(n : ℝ) * (θhat i n ω - θ i)‖ = √(n : ℝ) * ‖x - θ‖ := by
    have : (fun i ↦ √(n : ℝ) * (θhat i n ω - θ i)) = √(n : ℝ) • (x - θ) := by
      funext i
      simp [hx, smul_eq_mul]
    rw [this, norm_smul, Real.norm_of_nonneg (Real.sqrt_nonneg _)]
  have hk := hkey x
  rw [hL] at hk
  simp only [hnorm]
  have hsum : ∑ i, c i * (θhat i n ω - θ i) = ∑ i, c i * θhat i n ω - ∑ i, c i * θ i := by
    rw [← sum_sub_distrib]
    exact sum_congr rfl fun i _ ↦ by ring
  rw [hsum] at hk
  simp only [hx] at hk ⊢
  linear_combination (-√(n : ℝ)) * hk

/-- **The multivariate delta method with partial derivatives.** If `g` is differentiable at `θ`
and its restriction to the `i`th coordinate line through `θ` has derivative `d i` at `θ i`, then
`g (θhat · n)` is asymptotically linear at `g θ` with influence function `∑ i, d i φ i`. -/
theorem comp_of_partials {ι : Type*} [Fintype ι] [DecidableEq ι] [IsProbabilityMeasure μ]
    (hO : IsIIDSample O μ) {θhat : ι → ℕ → Ω → ℝ} {θ : ι → ℝ} {φ : ι → 𝒪 → ℝ}
    (h : ∀ i, IsAsymptoticallyLinear (θhat i) (θ i) (φ i) O μ)
    {g : (ι → ℝ) → ℝ} (hg : DifferentiableAt ℝ g θ) {d : ι → ℝ}
    (hd : ∀ i, HasDerivAt (fun t ↦ g (Function.update θ i t)) (d i) (θ i)) :
    IsAsymptoticallyLinear (fun n ω ↦ g (fun i ↦ θhat i n ω)) (g θ)
      (fun x ↦ ∑ i, d i * φ i x) O μ := by
  have h1 := comp_hasFDerivAt hO h hg.hasFDerivAt
  have hc : ∀ i, fderiv ℝ g θ (Pi.single i 1) = d i := by
    intro i
    have hg' : HasFDerivAt g (fderiv ℝ g θ) (Function.update θ i (θ i)) := by
      rw [Function.update_eq_self]
      exact hg.hasFDerivAt
    exact (hg'.comp_hasDerivAt (θ i) (hasDerivAt_update θ i (θ i))).unique (hd i)
  simp only [hc] at h1
  exact h1

end IsAsymptoticallyLinear

/-! ### The asymptotic variance -/

/-- The second moment of a linear combination: `E[(∑ i, cᵢ Zᵢ)²] = ∑ i, ∑ j, cᵢ cⱼ E[Zᵢ Zⱼ]` for
square integrable `Zᵢ`. -/
theorem integral_sq_sum_mul {ι : Type*} [Fintype ι] {μ : Measure Ω} {Z : ι → Ω → ℝ}
    (hZ : ∀ i, MemLp (Z i) 2 μ) (c : ι → ℝ) :
    μ[fun ω ↦ (∑ i, c i * Z i ω) ^ 2] = ∑ i, ∑ j, c i * c j * μ[fun ω ↦ Z i ω * Z j ω] := by
  have hexp : (fun ω ↦ (∑ i, c i * Z i ω) ^ 2) =
      fun ω ↦ ∑ i, ∑ j, c i * c j * (Z i ω * Z j ω) := by
    funext ω
    rw [sq, sum_mul_sum]
    refine sum_congr rfl fun i _ ↦ sum_congr rfl fun j _ ↦ ?_
    ring
  have hint : ∀ i j, Integrable (fun ω ↦ Z i ω * Z j ω) μ := fun i j ↦ (hZ i).integrable_mul (hZ j)
  rw [hexp, integral_finsetSum _ fun i _ ↦ integrable_finsetSum _ fun j _ ↦
    (hint i j).const_mul _]
  refine sum_congr rfl fun i _ ↦ ?_
  rw [integral_finsetSum _ fun j _ ↦ (hint i j).const_mul _]
  refine sum_congr rfl fun j _ ↦ ?_
  rw [integral_const_mul]

namespace IsAsymptoticallyLinear

variable {μ : Measure Ω} {O : ℕ → Ω → 𝒪}

/-- **Asymptotic variance: quadratic form in the covariance matrix.** For asymptotically linear
`θhat i` with influence functions `φ i`, the second moment of the influence function
`∑ i, cᵢ φ i` of the multivariate delta method is `∑ i, ∑ j, cᵢ cⱼ Cov(φ i (O), φ j (O))`: the
influence functions have mean zero, so their second moments are covariances. -/
theorem integral_sq_eq_sum_cov {ι : Type*} [Fintype ι] [IsProbabilityMeasure μ]
    {θhat : ι → ℕ → Ω → ℝ} {θ : ι → ℝ} {φ : ι → 𝒪 → ℝ}
    (h : ∀ i, IsAsymptoticallyLinear (θhat i) (θ i) (φ i) O μ) (c : ι → ℝ) :
    μ[fun ω ↦ (∑ i, c i * φ i (O 0 ω)) ^ 2] =
      ∑ i, ∑ j, c i * c j * cov[fun ω ↦ φ i (O 0 ω), fun ω ↦ φ j (O 0 ω); μ] := by
  rw [integral_sq_sum_mul (Z := fun i ω ↦ φ i (O 0 ω)) (fun i ↦ (h i).memLp) c]
  refine sum_congr rfl fun i _ ↦ sum_congr rfl fun j _ ↦ ?_
  rw [covariance_eq_sub (h i).memLp (h j).memLp, (h i).integral_eq_zero,
    (h j).integral_eq_zero, mul_zero, sub_zero]
  rfl

/-- **Asymptotic variance for independent influence functions.** If the influence functions are
pairwise independent at the observation (for instance because each estimate is computed from its
own independent component of the observation), the cross moments vanish and the second moment of
`∑ i, cᵢ φ i` is `∑ i, cᵢ² E[φ i (O)²]`: the sum of squared partial derivatives times the
asymptotic variances. -/
theorem integral_sq_of_indep {ι : Type*} [Fintype ι] [IsProbabilityMeasure μ]
    {θhat : ι → ℕ → Ω → ℝ} {θ : ι → ℝ} {φ : ι → 𝒪 → ℝ}
    (h : ∀ i, IsAsymptoticallyLinear (θhat i) (θ i) (φ i) O μ)
    (hind : Pairwise fun i j ↦ IndepFun (fun ω ↦ φ i (O 0 ω)) (fun ω ↦ φ j (O 0 ω)) μ)
    (c : ι → ℝ) :
    μ[fun ω ↦ (∑ i, c i * φ i (O 0 ω)) ^ 2] = ∑ i, c i ^ 2 * μ[fun ω ↦ φ i (O 0 ω) ^ 2] := by
  classical
  rw [integral_sq_sum_mul (Z := fun i ω ↦ φ i (O 0 ω)) (fun i ↦ (h i).memLp) c]
  refine sum_congr rfl fun i _ ↦ ?_
  rw [sum_eq_single i]
  · simp only [sq]
  · intro j _ hji
    have hm := IndepFun.integral_mul_eq_mul_integral (hind hji.symm)
      (h i).memLp.aestronglyMeasurable (h j).memLp.aestronglyMeasurable
    simp only [Pi.mul_apply] at hm
    rw [hm, (h i).integral_eq_zero]
    ring
  · intro hi
    exact absurd (mem_univ i) hi

/-- **Asymptotic normality in the multivariate delta method.** Under the hypotheses of
`comp_hasFDerivAt`, if each `g (θhat · n)` is almost everywhere measurable, then
`√n (g (θhat · n) - g θ)` converges in distribution to the centered Gaussian whose variance is
the quadratic form `∑ i, ∑ j, cᵢ cⱼ Cov(φ i (O), φ j (O))` of the gradient
`cᵢ = L (eᵢ)`. -/
theorem tendstoInDistribution_comp_hasFDerivAt {ι : Type*} [Fintype ι] [DecidableEq ι]
    [IsProbabilityMeasure μ] (hO : IsIIDSample O μ) {θhat : ι → ℕ → Ω → ℝ} {θ : ι → ℝ}
    {φ : ι → 𝒪 → ℝ} (h : ∀ i, IsAsymptoticallyLinear (θhat i) (θ i) (φ i) O μ)
    {g : (ι → ℝ) → ℝ} {L : (ι → ℝ) →L[ℝ] ℝ} (hg : HasFDerivAt g L θ)
    (hmeas : ∀ n, AEMeasurable (fun ω ↦ g (fun i ↦ θhat i n ω)) μ)
    {Ω' : Type*} {mΩ' : MeasurableSpace Ω'} {P' : Measure Ω'} [IsProbabilityMeasure P']
    {Y : Ω' → ℝ}
    (hY : HasLaw Y (gaussianReal 0 (∑ i, ∑ j, L (Pi.single i 1) * L (Pi.single j 1) *
      cov[fun ω ↦ φ i (O 0 ω), fun ω ↦ φ j (O 0 ω); μ]).toNNReal) P') :
    TendstoInDistribution (fun (n : ℕ) ω ↦ √n * (g (fun i ↦ θhat i n ω) - g θ)) atTop Y
      (fun _ ↦ μ) P' := by
  have hAL := comp_hasFDerivAt hO h hg
  refine hAL.tendstoInDistribution hO hmeas ?_
  rwa [integral_sq_eq_sum_cov h]

/-- **Two independent samples observed in pairs.** Let each observation be a pair
`O k = (A k, B k)` whose components are independent at the first observation, let `θhat₁` be
asymptotically linear with an influence function `φ₁` of the first component and `θhat₂` with an
influence function `φ₂` of the second, and let `g : (Fin 2 → ℝ) → ℝ` have derivative `L` at
`(θ₁, θ₂)`. Then `g (θhat₁, θhat₂)` is asymptotically linear with influence function
`c₀ φ₁ (a) + c₁ φ₂ (b)`, `cᵢ = L (eᵢ)`, and its asymptotic variance is
`c₀² E[φ₁(A)²] + c₁² E[φ₂(B)²]`: no covariance term appears. Both samples have the size `n` of
the paired sample. -/
theorem twoSample_integral_sq {𝒜 ℬ : Type*} [MeasurableSpace 𝒜] [MeasurableSpace ℬ]
    {P : ℕ → Ω → 𝒜 × ℬ} [IsProbabilityMeasure μ] (hO : IsIIDSample P μ)
    (hAB : IndepFun (fun ω ↦ (P 0 ω).1) (fun ω ↦ (P 0 ω).2) μ)
    {θhat₁ θhat₂ : ℕ → Ω → ℝ} {θ₁ θ₂ : ℝ} {φ₁ : 𝒜 → ℝ} {φ₂ : ℬ → ℝ}
    (h₁ : IsAsymptoticallyLinear θhat₁ θ₁ (fun x ↦ φ₁ x.1) P μ)
    (h₂ : IsAsymptoticallyLinear θhat₂ θ₂ (fun x ↦ φ₂ x.2) P μ)
    {g : (Fin 2 → ℝ) → ℝ} {L : (Fin 2 → ℝ) →L[ℝ] ℝ} (hg : HasFDerivAt g L ![θ₁, θ₂])
    (hφ₁ : Measurable φ₁) (hφ₂ : Measurable φ₂) :
    IsAsymptoticallyLinear (fun n ω ↦ g ![θhat₁ n ω, θhat₂ n ω]) (g ![θ₁, θ₂])
        (fun x ↦ L (Pi.single 0 1) * φ₁ x.1 + L (Pi.single 1 1) * φ₂ x.2) P μ ∧
      μ[fun ω ↦ (L (Pi.single 0 1) * φ₁ (P 0 ω).1 + L (Pi.single 1 1) * φ₂ (P 0 ω).2) ^ 2] =
        L (Pi.single 0 1) ^ 2 * μ[fun ω ↦ φ₁ (P 0 ω).1 ^ 2] +
          L (Pi.single 1 1) ^ 2 * μ[fun ω ↦ φ₂ (P 0 ω).2 ^ 2] := by
  set φ : Fin 2 → 𝒜 × ℬ → ℝ := ![fun x ↦ φ₁ x.1, fun x ↦ φ₂ x.2] with hφ
  have h : ∀ i, IsAsymptoticallyLinear (![θhat₁, θhat₂] i) (![θ₁, θ₂] i) (φ i) P μ := by
    intro i
    fin_cases i
    · exact h₁
    · exact h₂
  have hAL := comp_hasFDerivAt hO h hg
  have hθ : (fun i ↦ (![θ₁, θ₂] : Fin 2 → ℝ) i) = ![θ₁, θ₂] := rfl
  have hind : Pairwise fun i j ↦ IndepFun (fun ω ↦ φ i (P 0 ω)) (fun ω ↦ φ j (P 0 ω)) μ := by
    have h01 : IndepFun (fun ω ↦ φ 0 (P 0 ω)) (fun ω ↦ φ 1 (P 0 ω)) μ :=
      hAB.comp hφ₁ hφ₂
    intro i j hij
    fin_cases i <;> fin_cases j
    · exact absurd rfl hij
    · exact h01
    · exact h01.symm
    · exact absurd rfl hij
  have hvar := integral_sq_of_indep h hind (fun i ↦ L (Pi.single i 1))
  simp only [Fin.sum_univ_two, hφ, Matrix.cons_val_zero, Matrix.cons_val_one] at hAL hvar
  refine ⟨?_, hvar⟩
  convert hAL using 3 with n ω
  congr 1
  funext i
  fin_cases i <;> rfl

end IsAsymptoticallyLinear

end CausalInference
