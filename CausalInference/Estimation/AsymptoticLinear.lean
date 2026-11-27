/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.Estimation.Consistency
public import Mathlib.Probability.CentralLimitTheorem

/-!
# Asymptotically linear estimators

An estimator sequence `θhat` is asymptotically linear at `θ` with influence function `φ` when
`E φ(O) = 0`, `φ(O)` has a finite second moment, and the remainder
`√n (θhat n - θ) - n^{-1/2} ∑_{i < n} φ(O i)` tends to zero in probability.

Main results:

* `CausalInference.sampleMean_isAsymptoticallyLinear`: the sample mean of `f (O i)` with finite
  second moment is asymptotically linear with influence function `f - E f(O)`; the remainder is
  identically zero.
* `CausalInference.IsAsymptoticallyLinear.isConsistent`: an asymptotically linear estimator is
  consistent.
* `CausalInference.IsAsymptoticallyLinear.tendstoInDistribution`: **asymptotic normality**;
  `√n (θhat n - θ)` converges in distribution to `N(0, E φ(O)²)`. The proof combines the
  central limit theorem of Mathlib (`ProbabilityTheory.tendstoInDistribution_inv_sqrt_mul_sum_sub`)
  with the Slutsky-type lemma `MeasureTheory.tendstoInDistribution_of_tendstoInMeasure_sub`.
* `CausalInference.IsAsymptoticallyLinear.tendstoInDistribution_of_isSampleMeasurable`: the same
  for an estimator that is a measurable function of the first `n` observations.
* `CausalInference.IsAsymptoticallyLinear.ae_eq`: the influence function is unique: two influence
  functions of the same estimator at the same `θ` agree almost surely at the observation.
* `CausalInference.IsAsymptoticallyLinear.of_expansion`: an exact expansion
  `θhat n - θ = n⁻¹ ∑_{i < n} φ (O i) + r n` with `√n r n → 0` in probability gives asymptotic
  linearity; `IsAsymptoticallyLinear.add`, `.sub`, `.const_mul` and
  `.of_tendstoInMeasure_sqrt_mul_sub` give closure under sums, differences, scaling and
  `o_p(n^{-1/2})` perturbations.
* `CausalInference.exists_isAsymptoticallyLinear`: the hypotheses are satisfiable together: a
  standard Gaussian i.i.d. sample and its sample mean.

The predicate `IsAsymptoticallyLinear` is formed only for a probability measure.

Sources: A. W. van der Vaart (1998), *Asymptotic Statistics*, chapters 2, 3 and 5;
A. A. Tsiatis (2006), *Semiparametric Theory and Missing Data*, chapter 3.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Finset
open scoped Topology ENNReal NNReal

namespace CausalInference

variable {Ω 𝒪 : Type*} {mΩ : MeasurableSpace Ω} [MeasurableSpace 𝒪]

/-- The estimator sequence `θhat` is asymptotically linear at `θ` with influence function `φ`
for the sample `O` under the probability measure `μ`: `φ` is measurable, `φ (O 0)` is square
integrable with mean zero, and the remainder `√n (θhat n - θ) - n^{-1/2} ∑_{i < n} φ (O i)`
converges to `0` in probability.

The predicate is only formed for a probability measure `μ`. On an infinite measure a square
integrable `φ (O 0)` need not be integrable, and then the mean zero condition would hold by the
convention that the integral of a non-integrable function is `0`; on a probability measure the
second moment condition implies integrability, so the mean zero condition is genuine.

The predicate does not ask `θhat n` to depend only on the first `n` observations; the corollaries
with suffix `_of_isSampleMeasurable` add that requirement (`IsSampleMeasurable θhat O`). -/
structure IsAsymptoticallyLinear (θhat : ℕ → Ω → ℝ) (θ : ℝ) (φ : 𝒪 → ℝ) (O : ℕ → Ω → 𝒪)
    (μ : Measure Ω) [IsProbabilityMeasure μ] : Prop where
  /-- The influence function is measurable. -/
  measurable : Measurable φ
  /-- The influence function has a finite second moment at the observation. -/
  memLp : MemLp (fun ω ↦ φ (O 0 ω)) 2 μ
  /-- The influence function has mean zero at the observation. -/
  integral_eq_zero : μ[fun ω ↦ φ (O 0 ω)] = 0
  /-- The remainder of the linear expansion converges to zero in probability. -/
  remainder : TendstoInMeasure μ
    (fun (n : ℕ) ω ↦ √n * (θhat n ω - θ) - (√n)⁻¹ * ∑ i ∈ range n, φ (O i ω)) atTop 0

/-- `√n * n⁻¹ = (√n)⁻¹`, including at `n = 0`. -/
lemma sqrt_mul_inv_self (x : ℝ) : √x * x⁻¹ = (√x)⁻¹ := by
  rcases le_or_gt x 0 with hx | hx
  · simp [Real.sqrt_eq_zero'.2 hx]
  · have h := Real.sq_sqrt hx.le
    have h0 : √x ≠ 0 := (Real.sqrt_pos.2 hx).ne'
    field_simp
    linarith

/-- `(√n)⁻¹ * n = √n`, including at `n = 0`. -/
lemma inv_sqrt_mul_self (x : ℝ) (hx : 0 ≤ x) : (√x)⁻¹ * x = √x := by
  rcases hx.eq_or_lt with hx | hx
  · simp [← hx]
  · have h := Real.sq_sqrt hx.le
    have h0 : √x ≠ 0 := (Real.sqrt_pos.2 hx).ne'
    field_simp
    linarith

/-- **The sample mean is asymptotically linear.** If `μ` is a probability measure, `f` is
measurable and `f (O 0)` has a finite second moment, then the sample mean of
`f (O i)` is asymptotically linear at `E f (O 0)` with influence function `f - E f (O 0)`. The
remainder is identically zero. -/
theorem sampleMean_isAsymptoticallyLinear {μ : Measure Ω} [IsProbabilityMeasure μ]
    {O : ℕ → Ω → 𝒪} {f : 𝒪 → ℝ} (hf : Measurable f) (hf2 : MemLp (fun ω ↦ f (O 0 ω)) 2 μ) :
    IsAsymptoticallyLinear (sampleMean f O) (μ[fun ω ↦ f (O 0 ω)])
      (fun x ↦ f x - μ[fun ω ↦ f (O 0 ω)]) O μ where
  measurable := hf.sub_const _
  memLp := hf2.sub (memLp_const _)
  integral_eq_zero := by
    rw [integral_sub (hf2.integrable one_le_two) (integrable_const _)]
    simp
  remainder := by
    have h0 : (fun (n : ℕ) ω ↦ √n * (sampleMean f O n ω - μ[fun ω ↦ f (O 0 ω)]) -
        (√n)⁻¹ * ∑ i ∈ range n, (f (O i ω) - μ[fun ω ↦ f (O 0 ω)])) = fun _ _ ↦ 0 := by
      funext n ω
      simp only [sampleMean, sum_sub_distrib, sum_const, card_range, nsmul_eq_mul]
      have h1 := sqrt_mul_inv_self (n : ℝ)
      have h2 := inv_sqrt_mul_self (n : ℝ) n.cast_nonneg
      linear_combination (∑ i ∈ range n, f (O i ω)) * h1 + μ[fun ω ↦ f (O 0 ω)] * h2
    rw [h0, tendstoInMeasure_iff_norm]
    intro ε hε
    simp [not_le.2 hε]

namespace IsAsymptoticallyLinear

variable {θhat : ℕ → Ω → ℝ} {θ : ℝ} {φ : 𝒪 → ℝ} {O : ℕ → Ω → 𝒪} {μ : Measure Ω}

/-- An asymptotically linear estimator has an integrable influence function at the observation;
this is where the probability measure hypothesis of the predicate is used. -/
theorem integrable [IsProbabilityMeasure μ] (h : IsAsymptoticallyLinear θhat θ φ O μ) :
    Integrable (fun ω ↦ φ (O 0 ω)) μ :=
  h.memLp.integrable one_le_two

/-- **An asymptotically linear estimator is consistent.** The proof writes
`θhat n - θ = n⁻¹ ∑_{i < n} φ (O i) + n^{-1/2} R n` for `n ≥ 1`, where `R n` is the remainder;
the first term tends to `E φ (O 0) = 0` by the law of large numbers and the second is dominated
by `|R n|`. -/
theorem isConsistent [IsProbabilityMeasure μ] (hO : IsIIDSample O μ)
    (h : IsAsymptoticallyLinear θhat θ φ O μ) : IsConsistent θhat θ μ := by
  set R : ℕ → Ω → ℝ :=
    fun n ω ↦ √n * (θhat n ω - θ) - (√n)⁻¹ * ∑ i ∈ range n, φ (O i ω) with hR
  have hA : TendstoInMeasure μ (sampleMean φ O) atTop 0 := by
    have := sampleMean_isConsistent hO h.measurable h.integrable
    rw [IsConsistent, h.integral_eq_zero] at this
    exact this
  have hB : TendstoInMeasure μ (fun (n : ℕ) ω ↦ (√n)⁻¹ * R n ω) atTop 0 := by
    refine h.remainder.of_norm_le ?_
    filter_upwards [eventually_ge_atTop 1] with n hn ω
    rw [norm_mul]
    refine mul_le_of_le_one_left (norm_nonneg _) ?_
    rw [norm_inv, Real.norm_of_nonneg (Real.sqrt_nonneg _)]
    exact inv_le_one_of_one_le₀ (Real.one_le_sqrt.2 (by exact_mod_cast hn))
  have hsum := hA.add hB
  rw [add_zero] at hsum
  have hcongr : TendstoInMeasure μ (fun n ω ↦ θhat n ω - θ) atTop 0 := by
    refine TendstoInMeasure.congr' ?_ EventuallyEq.rfl hsum
    filter_upwards [eventually_ge_atTop 1] with n hn
    refine Eventually.of_forall fun ω ↦ ?_
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    have hs : √(n : ℝ) ≠ 0 := (Real.sqrt_pos.2 hn').ne'
    have hsq : √(n : ℝ) ^ 2 = n := Real.sq_sqrt hn'.le
    simp only [Pi.add_apply, sampleMean, hR]
    field_simp
    rw [hsq]
    ring
  rw [IsConsistent, tendstoInMeasure_iff_norm]
  rw [tendstoInMeasure_iff_norm] at hcongr
  simpa using hcongr

/-- **Asymptotic normality.** Let `θhat` be asymptotically linear at `θ` with influence function
`φ` for an i.i.d. sample `O` under a probability measure `μ`, with each `θhat n` almost everywhere
measurable. Then `√n (θhat n - θ)` converges in distribution to any random variable `Y` whose law
is the centered Gaussian `N(0, E φ (O 0)²)`. -/
theorem tendstoInDistribution [IsProbabilityMeasure μ] (hO : IsIIDSample O μ)
    (h : IsAsymptoticallyLinear θhat θ φ O μ) (hmeas : ∀ n, AEMeasurable (θhat n) μ)
    {Ω' : Type*} {mΩ' : MeasurableSpace Ω'} {P' : Measure Ω'} [IsProbabilityMeasure P']
    {Y : Ω' → ℝ} (hY : HasLaw Y (gaussianReal 0 (μ[fun ω ↦ φ (O 0 ω) ^ 2]).toNNReal) P') :
    TendstoInDistribution (fun (n : ℕ) ω ↦ √n * (θhat n ω - θ)) atTop Y (fun _ ↦ μ) P' := by
  have hφ := hO.comp h.measurable
  have hvar : Var[fun ω ↦ φ (O 0 ω); μ] = μ[fun ω ↦ φ (O 0 ω) ^ 2] :=
    variance_of_integral_eq_zero h.memLp.aemeasurable h.integral_eq_zero
  rw [← hvar] at hY
  have hclt := tendstoInDistribution_inv_sqrt_mul_sum_sub (X := fun i ω ↦ φ (O i ω)) hY h.memLp
    hφ.indep hφ.ident
  refine tendstoInDistribution_of_tendstoInMeasure_sub _ Y hclt ?_ ?_
  · convert h.remainder using 1
    funext n ω
    simp [h.integral_eq_zero]
  · exact fun n ↦ ((hmeas n).sub_const θ).const_mul _

/-- **Asymptotic normality for an estimator built from the sample.** The form of
`IsAsymptoticallyLinear.tendstoInDistribution` for an estimator `θhat` such that each `θhat n` is
a measurable function of the first `n` observations. -/
theorem tendstoInDistribution_of_isSampleMeasurable [IsProbabilityMeasure μ]
    (hO : IsIIDSample O μ) (h : IsAsymptoticallyLinear θhat θ φ O μ)
    (hθ : IsSampleMeasurable θhat O)
    {Ω' : Type*} {mΩ' : MeasurableSpace Ω'} {P' : Measure Ω'} [IsProbabilityMeasure P']
    {Y : Ω' → ℝ} (hY : HasLaw Y (gaussianReal 0 (μ[fun ω ↦ φ (O 0 ω) ^ 2]).toNNReal) P') :
    TendstoInDistribution (fun (n : ℕ) ω ↦ √n * (θhat n ω - θ)) atTop Y (fun _ ↦ μ) P' :=
  h.tendstoInDistribution hO (hθ.aemeasurable hO) hY

/-- **Uniqueness of the influence function.** If `θhat` is asymptotically linear at `θ` with
influence functions `φ` and `ψ` for an i.i.d. sample under a probability measure, then
`φ (O 0) = ψ (O 0)` almost surely. The difference `n^{-1/2} ∑_{i < n} (φ - ψ)(O i)` tends to zero
in probability, while by the central limit theorem it converges in distribution to
`N(0, Var((φ - ψ)(O 0)))`; uniqueness of limits in distribution forces the variance to vanish. -/
theorem ae_eq [IsProbabilityMeasure μ] {ψ : 𝒪 → ℝ} (hO : IsIIDSample O μ)
    (hφ : IsAsymptoticallyLinear θhat θ φ O μ) (hψ : IsAsymptoticallyLinear θhat θ ψ O μ) :
    ∀ᵐ ω ∂μ, φ (O 0 ω) = ψ (O 0 ω) := by
  have hm : Measurable fun x ↦ φ x - ψ x := hφ.measurable.sub hψ.measurable
  have hD := hO.comp hm
  have hL2 : MemLp (fun ω ↦ φ (O 0 ω) - ψ (O 0 ω)) 2 μ := hφ.memLp.sub hψ.memLp
  have hint : μ[fun ω ↦ φ (O 0 ω) - ψ (O 0 ω)] = 0 := by
    rw [integral_sub hφ.integrable hψ.integrable,
      hφ.integral_eq_zero, hψ.integral_eq_zero, sub_zero]
  set S : ℕ → Ω → ℝ := fun n ω ↦ (√n)⁻¹ *
    (∑ k ∈ range n, (φ (O k ω) - ψ (O k ω)) - n * μ[fun ω ↦ φ (O 0 ω) - ψ (O 0 ω)]) with hS
  have hSmeas : ∀ n, AEMeasurable (S n) μ := fun n ↦
    ((Finset.aemeasurable_fun_sum _ fun k _ ↦ (hD.aemeasurable k)).sub_const _).const_mul _
  -- `S n` tends to zero in probability.
  have hprob : TendstoInMeasure μ S atTop (fun _ ↦ 0) := by
    have := TendstoInMeasure.sub hψ.remainder hφ.remainder
    rw [sub_zero] at this
    convert this using 1
    funext n ω
    simp only [hS, hint, Pi.sub_apply, mul_zero, sub_zero, sum_sub_distrib]
    ring
  have hdist1 : TendstoInDistribution S atTop (fun _ ↦ (0 : ℝ)) (fun _ ↦ μ) μ :=
    hprob.tendstoInDistribution_of_aemeasurable hSmeas aemeasurable_const
  -- By the central limit theorem, `S n` converges to a centered Gaussian.
  set v : ℝ≥0 := (Var[fun ω ↦ φ (O 0 ω) - ψ (O 0 ω); μ]).toNNReal with hv
  have hdist2 : TendstoInDistribution S atTop id (fun _ ↦ μ) (gaussianReal 0 v) :=
    tendstoInDistribution_inv_sqrt_mul_sum_sub HasLaw.id hL2 hD.indep hD.ident
  have huniq := tendstoInDistribution_unique S hdist1 hdist2
  rw [Measure.map_const, measure_univ, one_smul, Measure.map_id, ← gaussianReal_zero_var,
    gaussianReal_ext_iff] at huniq
  have hvar0 : Var[fun ω ↦ φ (O 0 ω) - ψ (O 0 ω); μ] = 0 :=
    le_antisymm (Real.toNNReal_eq_zero.1 (hv ▸ huniq.2.symm)) (variance_nonneg _ _)
  filter_upwards [ae_eq_integral_of_variance_eq_zero hL2 hvar0] with ω hω
  rw [hint] at hω
  exact sub_eq_zero.1 hω

/-! ### Building asymptotically linear estimators -/

/-- **Asymptotic linearity from an exact expansion.** Let `μ` be a probability measure and `φ` a
measurable function with `φ (O 0)` square integrable and of mean zero. If eventually, for almost
every `ω`, `θhat n - θ = n⁻¹ ∑_{i < n} φ (O i) + r n` with a remainder satisfying
`√n r n → 0` in probability (that is, `r n = o_p(n^{-1/2})`), then `θhat` is asymptotically
linear at `θ` with influence function `φ`. -/
theorem of_expansion [IsProbabilityMeasure μ] (hφ : Measurable φ)
    (h2 : MemLp (fun ω ↦ φ (O 0 ω)) 2 μ) (h0 : μ[fun ω ↦ φ (O 0 ω)] = 0) {r : ℕ → Ω → ℝ}
    (hexp : ∀ᶠ n in atTop, ∀ᵐ ω ∂μ, θhat n ω - θ = sampleMean φ O n ω + r n ω)
    (hr : TendstoInMeasure μ (fun (n : ℕ) ω ↦ √n * r n ω) atTop 0) :
    IsAsymptoticallyLinear θhat θ φ O μ where
  measurable := hφ
  memLp := h2
  integral_eq_zero := h0
  remainder := by
    refine hr.congr' ?_ EventuallyEq.rfl
    filter_upwards [hexp] with n hn
    filter_upwards [hn] with ω hω
    have h1 := sqrt_mul_inv_self (n : ℝ)
    simp only [hω, sampleMean]
    linear_combination (-∑ i ∈ range n, φ (O i ω)) * h1

/-- **Invariance under negligible perturbations.** If `θhat` is asymptotically linear at `θ` with
influence function `φ` and `√n (θhat' n - θhat n) → 0` in probability (that is,
`θhat' n - θhat n = o_p(n^{-1/2})`), then `θhat'` is asymptotically linear at `θ` with the same
influence function. -/
theorem of_tendstoInMeasure_sqrt_mul_sub [IsProbabilityMeasure μ] {θhat' : ℕ → Ω → ℝ}
    (h : IsAsymptoticallyLinear θhat θ φ O μ)
    (hd : TendstoInMeasure μ (fun (n : ℕ) ω ↦ √n * (θhat' n ω - θhat n ω)) atTop 0) :
    IsAsymptoticallyLinear θhat' θ φ O μ where
  measurable := h.measurable
  memLp := h.memLp
  integral_eq_zero := h.integral_eq_zero
  remainder := by
    have := h.remainder.add hd
    rw [add_zero] at this
    convert this using 1
    funext n ω
    simp only [Pi.add_apply]
    ring

/-- **Sums of asymptotically linear estimators.** If `θhat` and `θhat'` are asymptotically linear
at `θ` and `θ'` with influence functions `φ` and `φ'` for the same sample, then
`θhat + θhat'` is asymptotically linear at `θ + θ'` with influence function `φ + φ'`. -/
theorem add [IsProbabilityMeasure μ] {θhat' : ℕ → Ω → ℝ} {θ' : ℝ} {φ' : 𝒪 → ℝ}
    (h : IsAsymptoticallyLinear θhat θ φ O μ) (h' : IsAsymptoticallyLinear θhat' θ' φ' O μ) :
    IsAsymptoticallyLinear (fun n ω ↦ θhat n ω + θhat' n ω) (θ + θ') (fun x ↦ φ x + φ' x) O μ where
  measurable := h.measurable.add h'.measurable
  memLp := h.memLp.add h'.memLp
  integral_eq_zero := by
    rw [integral_add h.integrable h'.integrable, h.integral_eq_zero, h'.integral_eq_zero, add_zero]
  remainder := by
    have := h.remainder.add h'.remainder
    rw [add_zero] at this
    convert this using 1
    funext n ω
    simp only [Pi.add_apply, sum_add_distrib]
    ring

/-- **Differences of asymptotically linear estimators.** If `θhat` and `θhat'` are asymptotically
linear at `θ` and `θ'` with influence functions `φ` and `φ'` for the same sample, then
`θhat - θhat'` is asymptotically linear at `θ - θ'` with influence function `φ - φ'`. -/
theorem sub [IsProbabilityMeasure μ] {θhat' : ℕ → Ω → ℝ} {θ' : ℝ} {φ' : 𝒪 → ℝ}
    (h : IsAsymptoticallyLinear θhat θ φ O μ) (h' : IsAsymptoticallyLinear θhat' θ' φ' O μ) :
    IsAsymptoticallyLinear (fun n ω ↦ θhat n ω - θhat' n ω) (θ - θ') (fun x ↦ φ x - φ' x) O μ where
  measurable := h.measurable.sub h'.measurable
  memLp := h.memLp.sub h'.memLp
  integral_eq_zero := by
    rw [integral_sub h.integrable h'.integrable, h.integral_eq_zero, h'.integral_eq_zero, sub_zero]
  remainder := by
    have := h.remainder.sub h'.remainder
    rw [sub_zero] at this
    convert this using 1
    funext n ω
    simp only [Pi.sub_apply, sum_sub_distrib]
    ring

/-- **Scaling an asymptotically linear estimator.** If `θhat` is asymptotically linear at `θ` with
influence function `φ`, then `c θhat` is asymptotically linear at `c θ` with influence function
`c φ`. -/
theorem const_mul [IsProbabilityMeasure μ] (c : ℝ) (h : IsAsymptoticallyLinear θhat θ φ O μ) :
    IsAsymptoticallyLinear (fun n ω ↦ c * θhat n ω) (c * θ) (fun x ↦ c * φ x) O μ where
  measurable := h.measurable.const_mul c
  memLp := h.memLp.const_mul c
  integral_eq_zero := by rw [integral_const_mul, h.integral_eq_zero, mul_zero]
  remainder := by
    refine (h.remainder.const_mul c).congr' (Eventually.of_forall fun n ↦
      Eventually.of_forall fun ω ↦ ?_) (Eventually.of_forall fun ω ↦ by simp)
    simp only [← mul_sum]
    ring

end IsAsymptoticallyLinear

/-- **Non-vacuity.** The hypotheses of the asymptotic linearity theorems can be met together:
there is an i.i.d. sample `O` of standard Gaussian observations under a probability measure, and
its sample mean is asymptotically linear at `0` with influence function `x ↦ x`. -/
theorem exists_isAsymptoticallyLinear :
    ∃ Ω : Type, ∃ _ : MeasurableSpace Ω, ∃ P : Measure Ω, ∃ O : ℕ → Ω → ℝ,
      ∃ _ : IsProbabilityMeasure P, IsIIDSample O P ∧ (∀ i, HasLaw (O i) (gaussianReal 0 1) P) ∧
        IsAsymptoticallyLinear (sampleMean (fun x ↦ x) O) 0 (fun x ↦ x) O P := by
  obtain ⟨Ω, _, P, O, hP, -, hO, hlaw⟩ := exists_isIIDSample (gaussianReal 0 1)
  refine ⟨Ω, _, P, O, hP, hO, hlaw, ?_⟩
  have hL2 : MemLp (fun ω ↦ O 0 ω) 2 P := (hlaw 0).memLp (memLp_id_gaussianReal 2)
  have hm : P[fun ω ↦ O 0 ω] = 0 := by
    rw [show (fun ω ↦ O 0 ω) = O 0 from rfl, (hlaw 0).integral_eq, integral_id_gaussianReal]
  have := sampleMean_isAsymptoticallyLinear (f := fun x ↦ x) measurable_id hL2
  rw [hm] at this
  simpa only [sub_zero] using this

end CausalInference
