/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.Designs.Randomized.Stratified

/-!
# Paired randomization

The units are grouped into `J` pairs by a stratum map `s : ι → σ` whose strata all have two
units, and within every pair exactly one unit is treated, each with probability `1/2`,
independently across pairs: stratified randomization with one treated unit per stratum. The
paired estimator is the mean of the within-pair differences `D_k` (treated minus control). We
show that it is unbiased, compute its exact variance, and show that the usual variance
estimator (the sample variance of the `D_k` divided by `J`) is conservative in expectation,
with equality under a constant pair-level effect. Sources: Imbens and Rubin (2015), *Causal
Inference for Statistics, Social, and Biomedical Sciences*, chapter 10.

## Main definitions

All declarations live in the namespace `CausalInference.Randomized`.

* `pairedDesign`: paired randomization as a `Design`.
* `PotentialOutcomes.pairDiff`: the within-pair difference `D_k`.
* `PotentialOutcomes.pairedEstimator`: the mean `(1/J) Σ_k D_k`.
* `PotentialOutcomes.pairEffect`: the effect `τ_k` within the pair `k`.
* `PotentialOutcomes.pairVar`: the variance of `D_k`, written with the potential outcomes.
* `PotentialOutcomes.pairedVarEstimator`: `(1/(J (J - 1))) Σ_k (D_k - D̄)²`.

## Main results

* `paired_estimator_unbiased`: the paired estimator is unbiased for the average treatment
  effect.
* `paired_estimator_variance`: its variance is `(1/J²) Σ_k pairVar k`.
* `paired_expect_varEstimator`: the expectation of the variance estimator is the true
  variance plus `(1/(J (J - 1))) Σ_k (τ_k - τ)²`.
* `paired_variance_le_expect_varEstimator`: the variance estimator is conservative.
* `paired_expect_varEstimator_eq_of_constant`: equality under a constant pair-level effect.
* `paired_fisher_pValue_valid`: Fisher's randomization test is valid under this design.
-/

@[expose] public section

namespace CausalInference.Randomized

open Finset

variable {ι σ : Type*} [Fintype ι] [DecidableEq ι] [Fintype σ] [DecidableEq σ]

omit [Fintype ι] [DecidableEq ι] in
/-- For any design, the variance is the mean of the square minus the square of the mean. -/
theorem Design.variance_eq_expect_sq_sub (d : Design ι) (f : (ι → Bool) → ℝ) :
    d.variance f = d.expect (fun a => f a ^ 2) - d.expect f ^ 2 := by
  rw [Design.variance, d.expect_congr (g := fun a => f a ^ 2 - (2 * d.expect f) * f a +
      d.expect f ^ 2) (fun _ _ => by ring), d.expect_add, d.expect_sub, d.expect_mul_left,
    d.expect_const]
  ring

/-- Paired randomization: the strata are pairs (every stratum has exactly two units), and
within every pair exactly one unit is treated, each with probability `1/2`, independently across
pairs. It is stratified randomization with one treated unit per stratum. -/
noncomputable def pairedDesign (s : ι → σ) (hs : ∀ k, stratumSize s k = 2) : Design ι :=
  stratifiedDesign s (fun _ => 1) (fun k => by rw [hs k]; norm_num)

/-- Under paired randomization every unit is treated with probability `1/2`. -/
theorem pairedDesign_inclusionProb (s : ι → σ) (hs : ∀ k, stratumSize s k = 2) (i : ι) :
    (pairedDesign s hs).inclusionProb i = 1 / 2 := by
  rw [pairedDesign, stratifiedDesign_inclusionProb, hs]
  norm_num

/-- Under paired randomization two units of different pairs are both treated with
probability `1/4`. -/
theorem pairedDesign_pairInclusionProb_of_ne (s : ι → σ) (hs : ∀ k, stratumSize s k = 2)
    {i j : ι} (hij : s i ≠ s j) : (pairedDesign s hs).pairInclusionProb i j = 1 / 4 := by
  rw [pairedDesign, stratifiedDesign_pairInclusionProb_of_ne _ _ _ hij,
    stratifiedDesign_inclusionProb, stratifiedDesign_inclusionProb, hs, hs]
  norm_num

namespace PotentialOutcomes

/-- The within-pair difference of the pair `k`: the observed outcome of its treated unit minus
that of its control unit, `Σ_{i ∈ k} (A_i Y_i - (1 - A_i) Y_i)`. -/
noncomputable def pairDiff (po : PotentialOutcomes ι) (s : ι → σ) (k : σ) (a : ι → Bool) : ℝ :=
  ∑ i ∈ stratum s k, (treatInd a i * po.observed a i - (1 - treatInd a i) * po.observed a i)

/-- The paired estimator: the mean `(1/J) Σ_k D_k` of the within-pair differences over the `J`
pairs. -/
noncomputable def pairedEstimator (po : PotentialOutcomes ι) (s : ι → σ) (a : ι → Bool) : ℝ :=
  popMean fun k => po.pairDiff s k a

/-- The average treatment effect `τ_k = (1/2) Σ_{i ∈ k} (y1 i - y0 i)` within the pair `k`. -/
noncomputable def pairEffect (po : PotentialOutcomes ι) (s : ι → σ) (k : σ) : ℝ :=
  (1 / 2) * ∑ i ∈ stratum s k, po.unitEffect i

/-- The randomization variance of the within-pair difference of the pair `k`, written with
`c i = y1 i + y0 i`: `(1/2) Σ_{i ∈ k} (c i - c̄_k)²`, with `c̄_k` the mean of `c` over the pair.
For a pair `{u, v}` it equals `(c u - c v)² / 4`. -/
noncomputable def pairVar (po : PotentialOutcomes ι) (s : ι → σ) (k : σ) : ℝ :=
  (1 / 2) * ∑ i ∈ stratum s k,
    (po.y1 i + po.y0 i - (1 / 2) * ∑ j ∈ stratum s k, (po.y1 j + po.y0 j)) ^ 2

/-- The usual variance estimator for the paired estimator: the sample variance of the `J`
within-pair differences divided by `J`, that is `(1/(J (J - 1))) Σ_k (D_k - D̄)²`. -/
noncomputable def pairedVarEstimator (po : PotentialOutcomes ι) (s : ι → σ) (a : ι → Bool) :
    ℝ :=
  ((Fintype.card σ : ℝ) * (Fintype.card σ - 1))⁻¹ *
    ∑ k, (po.pairDiff s k a - po.pairedEstimator s a) ^ 2

omit [DecidableEq ι] [Fintype σ] in
/-- The within-pair difference is affine in the treatment indicators:
`D_k = Σ_{i ∈ k} (A_i (y1 i + y0 i) - y0 i)`. -/
theorem pairDiff_eq (po : PotentialOutcomes ι) (s : ι → σ) (k : σ) (a : ι → Bool) :
    po.pairDiff s k a = ∑ i ∈ stratum s k, (treatInd a i * (po.y1 i + po.y0 i) - po.y0 i) := by
  refine sum_congr rfl fun i _ => ?_
  unfold treatInd observed
  split_ifs <;> ring

omit [DecidableEq ι] [Fintype σ] in
/-- The pair effect as a sum: `τ_k = Σ_{i ∈ k} ((y1 i + y0 i) / 2 - y0 i)`. -/
theorem pairEffect_eq (po : PotentialOutcomes ι) (s : ι → σ) (k : σ) :
    po.pairEffect s k = ∑ i ∈ stratum s k, (1 / 2 * (po.y1 i + po.y0 i) - po.y0 i) := by
  rw [pairEffect, mul_sum]
  refine sum_congr rfl fun i _ => ?_
  unfold unitEffect
  ring

end PotentialOutcomes

/-- Under paired randomization the within-pair difference of the pair `k` has mean `τ_k`. -/
theorem paired_expect_pairDiff (po : PotentialOutcomes ι) (s : ι → σ)
    (hs : ∀ k, stratumSize s k = 2) (k : σ) :
    (pairedDesign s hs).expect (po.pairDiff s k) = po.pairEffect s k := by
  set d := pairedDesign s hs
  rw [show po.pairDiff s k = _ from funext (po.pairDiff_eq s k), d.expect_sum,
    po.pairEffect_eq]
  refine sum_congr rfl fun i _ => ?_
  rw [d.expect_congr (g := fun a => (po.y1 i + po.y0 i) * treatInd a i - po.y0 i)
      (fun _ _ => by ring), d.expect_sub, d.expect_mul_left, d.expect_const]
  change _ * d.inclusionProb i - _ = _
  rw [pairedDesign_inclusionProb]
  ring

/-- Under paired randomization the variance of the within-pair difference of the pair `k` is
`pairVar k`; for the pair `{u, v}` this is `((y1 u + y0 u) - (y1 v + y0 v))² / 4`. -/
theorem paired_variance_pairDiff (po : PotentialOutcomes ι) (s : ι → σ)
    (hs : ∀ k, stratumSize s k = 2) (k : σ) :
    (pairedDesign s hs).variance (po.pairDiff s k) = po.pairVar s k := by
  set d := pairedDesign s hs
  obtain ⟨u, v, huv, hk⟩ := card_eq_two.mp (hs k)
  rw [d.variance_eq_of_expect _ _ (paired_expect_pairDiff po s hs k)]
  have hpt : ∀ a ∈ d.support, (po.pairDiff s k a - po.pairEffect s k) ^ 2 =
      (po.y1 u + po.y0 u - (po.y1 v + po.y0 v)) ^ 2 / 4 := by
    intro a ha
    have h1 : treatInd a u + treatInd a v = 1 := by
      have h' := numTreatedIn_eq_sum s k a
      rw [(mem_stratifiedSupport.mp ha) k, hk, sum_pair huv] at h'
      push_cast at h'
      linarith
    rw [po.pairDiff_eq, po.pairEffect_eq, hk, sum_pair huv, sum_pair huv,
      show treatInd a v = 1 - treatInd a u by linarith]
    unfold treatInd
    split_ifs <;> ring
  rw [d.expect_congr hpt, d.expect_const, PotentialOutcomes.pairVar, hk, sum_pair huv,
    sum_pair huv]
  ring

/-- Under paired randomization the within-pair differences of distinct pairs are uncorrelated:
`E[D_k D_l] = τ_k τ_l` for `k ≠ l`. -/
theorem paired_expect_pairDiff_mul_of_ne (po : PotentialOutcomes ι) (s : ι → σ)
    (hs : ∀ k, stratumSize s k = 2) {k l : σ} (hkl : k ≠ l) :
    (pairedDesign s hs).expect (fun a => po.pairDiff s k a * po.pairDiff s l a) =
      po.pairEffect s k * po.pairEffect s l := by
  set d := pairedDesign s hs
  simp only [po.pairDiff_eq, po.pairEffect_eq, sum_mul_sum]
  rw [d.expect_sum]
  refine sum_congr rfl fun i hi => ?_
  rw [d.expect_sum]
  refine sum_congr rfl fun j hj => ?_
  have hij : s i ≠ s j := by rw [mem_stratum.mp hi, mem_stratum.mp hj]; exact hkl
  set ci := po.y1 i + po.y0 i
  set cj := po.y1 j + po.y0 j
  rw [d.expect_congr (g := fun a => ci * cj * (treatInd a i * treatInd a j) -
      (ci * po.y0 j) * treatInd a i - (cj * po.y0 i) * treatInd a j + po.y0 i * po.y0 j)
      (fun _ _ => by ring), d.expect_add, d.expect_sub, d.expect_sub, d.expect_mul_left,
    d.expect_mul_left, d.expect_mul_left, d.expect_const]
  change ci * cj * d.pairInclusionProb i j - ci * po.y0 j * d.inclusionProb i -
    cj * po.y0 i * d.inclusionProb j + _ = _
  rw [pairedDesign_pairInclusionProb_of_ne s hs hij, pairedDesign_inclusionProb,
    pairedDesign_inclusionProb]
  ring

/-- The second moments of the within-pair differences under paired randomization:
`E[D_k D_l] = (pairVar k if k = l, else 0) + τ_k τ_l`. -/
theorem paired_expect_pairDiff_mul (po : PotentialOutcomes ι) (s : ι → σ)
    (hs : ∀ k, stratumSize s k = 2) (k l : σ) :
    (pairedDesign s hs).expect (fun a => po.pairDiff s k a * po.pairDiff s l a) =
      (if k = l then po.pairVar s k else 0) + po.pairEffect s k * po.pairEffect s l := by
  by_cases hkl : k = l
  · subst hkl
    have := (pairedDesign s hs).variance_eq_expect_sq_sub (po.pairDiff s k)
    rw [paired_variance_pairDiff, paired_expect_pairDiff] at this
    simp only [ite_true, ← sq]
    linarith
  · simp [paired_expect_pairDiff_mul_of_ne po s hs hkl, hkl]

omit [DecidableEq ι] in
/-- With `J` pairs the average treatment effect is the mean of the pair effects:
`τ = (1/J) Σ_k τ_k`. -/
theorem ate_eq_popMean_pairEffect (po : PotentialOutcomes ι) (s : ι → σ)
    (hs : ∀ k, stratumSize s k = 2) : po.ate = popMean (po.pairEffect s) := by
  have hN : (Fintype.card ι : ℝ) = 2 * Fintype.card σ := by
    have := card_eq_sum_card_fiberwise (s := (univ : Finset ι)) (t := univ) (f := s)
      (fun _ _ => mem_univ _)
    simp only [card_univ] at this
    rw [this]
    have h2 : ∀ k, #({i ∈ univ | s i = k} : Finset ι) = 2 := hs
    simp only [h2, sum_const, card_univ, smul_eq_mul]
    push_cast
    ring
  rw [PotentialOutcomes.ate, popMean, popMean, hN, ← sum_fiberwise univ s po.unitEffect]
  simp only [PotentialOutcomes.pairEffect, ← mul_sum]
  rw [mul_inv]
  ring_nf
  rfl

/-- **Unbiasedness of the paired estimator.** Under paired randomization the mean of the
within-pair differences (treated minus control) is unbiased for the average treatment effect.
-/
theorem paired_estimator_unbiased (po : PotentialOutcomes ι) (s : ι → σ)
    (hs : ∀ k, stratumSize s k = 2) :
    (pairedDesign s hs).expect (po.pairedEstimator s) = po.ate := by
  rw [ate_eq_popMean_pairEffect po s hs]
  rw [show po.pairedEstimator s = fun a => (Fintype.card σ : ℝ)⁻¹ * ∑ k, po.pairDiff s k a
    from rfl, popMean, Design.expect_mul_left, Design.expect_sum]
  simp only [paired_expect_pairDiff]

/-- The second moment of the sum of the within-pair differences:
`E[(Σ_k D_k)²] = Σ_k pairVar k + (Σ_k τ_k)²`. -/
theorem paired_expect_sum_sq (po : PotentialOutcomes ι) (s : ι → σ)
    (hs : ∀ k, stratumSize s k = 2) :
    (pairedDesign s hs).expect (fun a => (∑ k, po.pairDiff s k a) ^ 2) =
      ∑ k, po.pairVar s k + (∑ k, po.pairEffect s k) ^ 2 := by
  simp only [sq, sum_mul_sum, Design.expect_sum, paired_expect_pairDiff_mul, sum_add_distrib,
    sum_ite_eq, mem_univ, ite_true]

/-- **Exact variance of the paired estimator.** Under paired randomization with `J` pairs, the
variance of the mean of the within-pair differences is `(1/J²) Σ_k pairVar k`, where for the
pair `{u, v}`, `pairVar k = ((y1 u + y0 u) - (y1 v + y0 v))² / 4`. -/
theorem paired_estimator_variance (po : PotentialOutcomes ι) (s : ι → σ)
    (hs : ∀ k, stratumSize s k = 2) :
    (pairedDesign s hs).variance (po.pairedEstimator s) =
      ((Fintype.card σ : ℝ) ^ 2)⁻¹ * ∑ k, po.pairVar s k := by
  rw [Design.variance_eq_expect_sq_sub, paired_estimator_unbiased,
    ate_eq_popMean_pairEffect po s hs,
    show (fun a => po.pairedEstimator s a ^ 2) =
      fun a => ((Fintype.card σ : ℝ)⁻¹) ^ 2 * (∑ k, po.pairDiff s k a) ^ 2 from
      funext fun a => by simp only [PotentialOutcomes.pairedEstimator, popMean, mul_pow],
    Design.expect_mul_left, paired_expect_sum_sq, popMean]
  ring

/-- **Expectation of the paired variance estimator.** Under paired randomization with `J ≥ 2`
pairs, the expectation of the variance estimator `(1/(J (J - 1))) Σ_k (D_k - D̄)²` is the true
variance of the paired estimator plus `(1/(J (J - 1))) Σ_k (τ_k - τ)²`, where `τ_k` is the
effect within the pair `k` and `τ` the average treatment effect. -/
theorem paired_expect_varEstimator (po : PotentialOutcomes ι) (s : ι → σ)
    (hs : ∀ k, stratumSize s k = 2) (hJ : 1 < Fintype.card σ) :
    (pairedDesign s hs).expect (po.pairedVarEstimator s) =
      (pairedDesign s hs).variance (po.pairedEstimator s) +
        ((Fintype.card σ : ℝ) * (Fintype.card σ - 1))⁻¹ *
          ∑ k, (po.pairEffect s k - po.ate) ^ 2 := by
  have hJ0 : 0 < Fintype.card σ := by omega
  have hJr : (Fintype.card σ : ℝ) ≠ 0 := by exact_mod_cast hJ0.ne'
  have hJ1 : (Fintype.card σ : ℝ) - 1 ≠ 0 := by
    have : (1 : ℝ) < Fintype.card σ := by exact_mod_cast hJ
    linarith
  have hrw : ∀ a, po.pairedVarEstimator s a =
      ((Fintype.card σ : ℝ) * (Fintype.card σ - 1))⁻¹ *
        (∑ k, po.pairDiff s k a ^ 2 - (Fintype.card σ : ℝ)⁻¹ * (∑ k, po.pairDiff s k a) ^ 2) :=
    fun a => by
      rw [PotentialOutcomes.pairedVarEstimator, PotentialOutcomes.pairedEstimator,
        sum_sq_sub_popMean _ hJ0]
  have hk2 : ∀ k, (pairedDesign s hs).expect (fun a => po.pairDiff s k a ^ 2) =
      po.pairVar s k + po.pairEffect s k ^ 2 := fun k => by
    rw [show (fun a => po.pairDiff s k a ^ 2) = fun a => po.pairDiff s k a * po.pairDiff s k a
      from funext fun a => sq _, paired_expect_pairDiff_mul]
    simp only [ite_true]
    ring
  rw [show po.pairedVarEstimator s = _ from funext hrw, Design.expect_mul_left,
    Design.expect_sub, Design.expect_mul_left, Design.expect_sum, paired_expect_sum_sq,
    paired_estimator_variance, ate_eq_popMean_pairEffect po s hs, sum_sq_sub_popMean _ hJ0]
  simp only [hk2, sum_add_distrib]
  field_simp
  ring

/-- **The paired variance estimator is conservative.** Under paired randomization with
`J ≥ 2` pairs, the expectation of the variance estimator is at least the true variance of the
paired estimator. -/
theorem paired_variance_le_expect_varEstimator (po : PotentialOutcomes ι) (s : ι → σ)
    (hs : ∀ k, stratumSize s k = 2) (hJ : 1 < Fintype.card σ) :
    (pairedDesign s hs).variance (po.pairedEstimator s) ≤
      (pairedDesign s hs).expect (po.pairedVarEstimator s) := by
  rw [paired_expect_varEstimator po s hs hJ]
  have : (1 : ℝ) < Fintype.card σ := by exact_mod_cast hJ
  have h1 : 0 ≤ ((Fintype.card σ : ℝ) * (Fintype.card σ - 1))⁻¹ :=
    inv_nonneg.mpr (mul_nonneg (by linarith) (by linarith))
  have h2 : 0 ≤ ∑ k, (po.pairEffect s k - po.ate) ^ 2 := sum_nonneg fun _ _ => sq_nonneg _
  nlinarith

/-- **Equality under a constant pair-level effect.** If every pair has the same effect
`τ_k = c`, the expectation of the paired variance estimator equals the true variance. -/
theorem paired_expect_varEstimator_eq_of_constant (po : PotentialOutcomes ι) (s : ι → σ)
    (hs : ∀ k, stratumSize s k = 2) (hJ : 1 < Fintype.card σ) (c : ℝ)
    (hc : ∀ k, po.pairEffect s k = c) :
    (pairedDesign s hs).expect (po.pairedVarEstimator s) =
      (pairedDesign s hs).variance (po.pairedEstimator s) := by
  have hate : po.ate = c := by
    have hJr : (Fintype.card σ : ℝ) ≠ 0 := by exact_mod_cast (by omega : Fintype.card σ ≠ 0)
    rw [ate_eq_popMean_pairEffect po s hs, popMean]
    simp only [hc, sum_const, card_univ, nsmul_eq_mul]
    field_simp
  rw [paired_expect_varEstimator po s hs hJ]
  simp [hc, hate]

/-- **Fisher's test under paired randomization.** Under the sharp null the Fisher
randomization p-value computed with the paired design is valid. -/
theorem paired_fisher_pValue_valid (po : PotentialOutcomes ι) (hnull : po.SharpNull)
    (s : ι → σ) (hs : ∀ k, stratumSize s k = 2) (T : (ι → Bool) → (ι → ℝ) → ℝ)
    {α : ℝ} (hα : 0 ≤ α) :
    (pairedDesign s hs).prob
      (fun a => (pairedDesign s hs).fisherPValue T (po.observed a) a ≤ α) ≤ α :=
  fisher_pValue_valid po hnull _ T hα

end CausalInference.Randomized
