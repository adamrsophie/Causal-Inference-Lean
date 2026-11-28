/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.PopulationAdjustment.TiltWeights
public import CausalInference.IndirectComparison.CommonComparator
public import CausalInference.PointTreatment.Weighting
public import Mathlib.Algebra.Order.Chebyshev
public import Mathlib.Probability.Moments.Covariance

/-!
# Population adjustment: the effective sample size of a weight vector

The **effective sample size** of real weights `w₁, …, wₙ` is Kish's
`ESS = (∑ᵢ wᵢ)² / ∑ᵢ wᵢ²` (`ess`). It is the sample size of an unweighted mean with the same
variance as the weighted mean: for uncorrelated outcomes with common variance `σ²`, the
weighted mean `∑ᵢ wᵢ Yᵢ / ∑ᵢ wᵢ` has variance `σ² / ESS` (`variance_weightedMean`), so the
variance inflation of the weighting is `n / ESS` (`variance_weightedMean_div`).

* **Bounds.** For weights not all zero, `ESS ≤ n` (Cauchy and Schwarz against the vector of
  ones), with equality exactly when all the weights are equal (`ess_le_card`, `ess_eq_card_iff`);
  for nonnegative weights `ESS ≥ 1` (`one_le_ess`). Rescaling leaves it unchanged (`ess_smul`).
* **The population form.** The library's `PointTreatment.essFraction ν w = E[w]² / E[w²]` is the
  effective sample size fraction of a weight function under a law `ν`. Under the empirical law of
  a sample it is `ESS / n` (`essFraction_ipdEmpirical`); under a probability law it is at most one
  (`essFraction_le_one`), with equality exactly when `w` has variance zero.
* **Variance inflation.** `n / ESS ≥ 1`, with equality exactly when the weights are equal
  (`one_le_card_div_ess`, `card_div_ess_eq_one_iff`).

No sign condition on the weights is needed for the variance identity: only a nonzero total
weight. All statements that divide by `∑ wᵢ²` assume it positive.

## Main definitions

* `ess w = (∑ᵢ wᵢ)² / ∑ᵢ wᵢ²`.
* `weightedMean w y = ∑ᵢ wᵢ yᵢ / ∑ᵢ wᵢ`.

## Main results

* `sum_sq_pos_iff`, `ess_pos`, `ess_le_card`, `ess_eq_card_iff`, `one_le_ess`, `ess_smul`.
* `essFraction_ipdEmpirical`, `essFraction_le_one`, `essFraction_eq_one_iff`.
* `integral_weightedMean`, `variance_weightedMean`, `variance_weightedMean_div`,
  `one_le_card_div_ess`, `card_div_ess_eq_one_iff`.
* `variance_weightedMean_example`: two independent fair signs with weights `1` and `2`:
  `ESS = 9/5` and variance `5/9`.

## References

* L. Kish, *Survey Sampling*, Wiley, 1965.
-/

@[expose] public section

namespace CausalInference

namespace PopulationAdjustment

open MeasureTheory ProbabilityTheory Finset IndirectComparison

/-! ### Definition and bounds -/

section Bounds

variable {ι : Type*} [Fintype ι] (w : ι → ℝ)

/-- The **effective sample size** `(∑ᵢ wᵢ)² / ∑ᵢ wᵢ²` of the weights `w` (Kish). The results
assume `0 < ∑ᵢ wᵢ²`. -/
noncomputable def ess : ℝ := (∑ i, w i) ^ 2 / ∑ i, w i ^ 2

variable {w}

/-- The sum of squared weights is positive exactly when some weight is nonzero. -/
theorem sum_sq_pos_iff : 0 < ∑ i, w i ^ 2 ↔ ∃ i, w i ≠ 0 := by
  constructor
  · intro h
    by_contra hne
    push Not at hne
    simp [hne] at h
  · rintro ⟨i, hi⟩
    exact Finset.sum_pos' (fun j _ => sq_nonneg (w j)) ⟨i, mem_univ _, by positivity⟩

/-- A nonzero total weight gives a positive sum of squared weights. -/
theorem sum_sq_pos_of_sum_ne_zero (hw : ∑ i, w i ≠ 0) : 0 < ∑ i, w i ^ 2 := by
  refine sum_sq_pos_iff.2 ?_
  by_contra hne
  push Not at hne
  exact hw (by simp [hne])

/-- A nonzero total weight gives a positive effective sample size. -/
theorem ess_pos (hw : ∑ i, w i ≠ 0) : 0 < ess w :=
  div_pos (by positivity) (sum_sq_pos_of_sum_ne_zero hw)

/-- **The effective sample size is at most the sample size**: `ESS ≤ n` for real weights with a
positive sum of squares, by `(∑ wᵢ)² ≤ n ∑ wᵢ²`. -/
theorem ess_le_card (h : 0 < ∑ i, w i ^ 2) : ess w ≤ Fintype.card ι := by
  rw [ess, div_le_iff₀ h]
  simpa using sq_sum_le_card_mul_sum_sq (s := (univ : Finset ι)) (f := w)

/-- Lagrange's identity `∑ᵢ ∑ⱼ (wᵢ - wⱼ)² = 2 (n ∑ wᵢ² - (∑ wᵢ)²)`. -/
theorem sum_sum_sub_sq :
    ∑ i, ∑ j, (w i - w j) ^ 2 =
      2 * (Fintype.card ι * ∑ i, w i ^ 2 - (∑ i, w i) ^ 2) := by
  simp only [sub_sq, Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_const,
    Finset.card_univ, nsmul_eq_mul, ← Finset.mul_sum, ← Finset.sum_mul]
  ring

/-- **The equality case**: for a positive sum of squares, `ESS = n` exactly when all the weights
are equal. -/
theorem ess_eq_card_iff (h : 0 < ∑ i, w i ^ 2) :
    ess w = Fintype.card ι ↔ ∀ i j, w i = w j := by
  have key := sum_sum_sub_sq (w := w)
  have hnn : ∀ i ∈ (univ : Finset ι), 0 ≤ ∑ j, (w i - w j) ^ 2 :=
    fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg _
  rw [ess, div_eq_iff h.ne']
  constructor
  · intro he i j
    have h0 : ∑ i, ∑ j, (w i - w j) ^ 2 = 0 := by rw [key, he]; ring
    have hi := (Finset.sum_eq_zero_iff_of_nonneg hnn).1 h0 i (mem_univ _)
    have hij := (Finset.sum_eq_zero_iff_of_nonneg fun j _ => sq_nonneg (w i - w j)).1 hi j
      (mem_univ _)
    exact sub_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 hij)
  · intro he
    have h0 : ∑ i, ∑ j, (w i - w j) ^ 2 = 0 :=
      Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ => by rw [he i j]; ring
    linarith

/-- **Nonnegative weights have an effective sample size of at least one**, since
`∑ wᵢ² ≤ (∑ wᵢ)²` for nonnegative weights. -/
theorem one_le_ess (hw : ∀ i, 0 ≤ w i) (h : 0 < ∑ i, w i ^ 2) : 1 ≤ ess w := by
  rw [ess, one_le_div h]
  exact Finset.sum_sq_le_sq_sum_of_nonneg fun i _ => hw i

/-- **The effective sample size is invariant under rescaling** by a nonzero constant. -/
theorem ess_smul {a : ℝ} (ha : a ≠ 0) (h : 0 < ∑ i, w i ^ 2) :
    ess (fun i => a * w i) = ess w := by
  have ha2 : 0 < a ^ 2 := by positivity
  simp only [ess, ← Finset.mul_sum, mul_pow]
  field_simp

/-- The effective sample size of the normalized weights is that of the weights. -/
theorem ess_normalizedWeights (hw : ∑ i, w i ≠ 0) (h : 0 < ∑ i, w i ^ 2) :
    ess (normalizedWeights w) = ess w := by
  have : normalizedWeights w = fun i => (∑ j, w j)⁻¹ * w i := by
    funext i; rw [normalizedWeights, div_eq_inv_mul]
  rw [this, ess_smul (inv_ne_zero hw) h]

/-- **Variance inflation is at least one**: `n / ESS ≥ 1` for a nonzero total weight. -/
theorem one_le_card_div_ess (hw : ∑ i, w i ≠ 0) : 1 ≤ Fintype.card ι / ess w := by
  have h2 := sum_sq_pos_of_sum_ne_zero hw
  exact (one_le_div (ess_pos hw)).2 (ess_le_card h2)

/-- The variance inflation `n / ESS` is one exactly when the weights are equal (nonzero total
weight). -/
theorem card_div_ess_eq_one_iff (hw : ∑ i, w i ≠ 0) :
    Fintype.card ι / ess w = 1 ↔ ∀ i j, w i = w j := by
  have h2 := sum_sq_pos_of_sum_ne_zero hw
  rw [div_eq_one_iff_eq (ess_pos hw).ne', eq_comm]
  exact ess_eq_card_iff h2

end Bounds

/-! ### The population form -/

section Population

variable {𝒳 ι' : Type*} [MeasurableSpace 𝒳] [MeasurableSpace ι'] [MeasurableSingletonClass 𝒳]
  [MeasurableSingletonClass ι'] {n : ℕ}

/-- **The effective sample size fraction of the empirical law** is `ESS / n`: for a nonempty
sample and any weight function `f` of the observations,
`essFraction (ipdEmpirical x a y) f = ess (f(xᵢ, aᵢ, yᵢ))ᵢ / n`. -/
theorem essFraction_ipdEmpirical (hn : 0 < n) (x : Fin n → 𝒳) (a : Fin n → ι') (y : Fin n → ℝ)
    (f : 𝒳 × ι' × ℝ → ℝ) :
    PointTreatment.essFraction (Trial.ipdEmpirical x a y) f =
      ess (fun i => f (x i, a i, y i)) / n := by
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  rw [PointTreatment.essFraction, integral_ipdEmpirical, integral_ipdEmpirical, ess]
  rcases eq_or_ne (∑ i, f (x i, a i, y i) ^ 2) 0 with h0 | h0
  · simp [h0]
  · field_simp

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
  {w : Ω → ℝ}

/-- **The effective sample size fraction of a weight function is at most one** under a
probability law, for a square integrable weight with `E[w²] > 0`. This is `E[w]² ≤ E[w²]`. -/
theorem essFraction_le_one (hw : MemLp w 2 μ) (h : 0 < ∫ ω, w ω ^ 2 ∂μ) :
    PointTreatment.essFraction μ w ≤ 1 := by
  rw [PointTreatment.essFraction, div_le_one h]
  have hv := variance_nonneg w μ
  rw [variance_eq_sub hw] at hv
  simpa using hv

/-- The effective sample size fraction is one exactly when the weight has variance zero (it is
almost surely constant). -/
theorem essFraction_eq_one_iff (hw : MemLp w 2 μ) (h : 0 < ∫ ω, w ω ^ 2 ∂μ) :
    PointTreatment.essFraction μ w = 1 ↔ Var[w; μ] = 0 := by
  rw [PointTreatment.essFraction, div_eq_one_iff_eq h.ne', variance_eq_sub hw]
  simp only [Pi.pow_apply]
  constructor <;> intro h' <;> linarith

end Population

/-! ### The variance of a weighted mean -/

section Variance

variable {ι : Type*} [Fintype ι]

/-- The **weighted mean** `∑ᵢ wᵢ yᵢ / ∑ᵢ wᵢ`. The results assume a nonzero total weight. -/
noncomputable def weightedMean (w y : ι → ℝ) : ℝ := (∑ i, w i * y i) / ∑ i, w i

/-- The weighted mean is the normalized weights' combination `∑ᵢ (wᵢ / ∑ⱼ wⱼ) yᵢ`. -/
theorem weightedMean_eq_sum_normalizedWeights (w y : ι → ℝ) :
    weightedMean w y = ∑ i, normalizedWeights w i * y i := by
  simp only [weightedMean, normalizedWeights, Finset.sum_div, div_mul_eq_mul_div]

/-- A nonzero factor of the weights cancels in the weighted mean. -/
theorem weightedMean_smul {a : ℝ} (ha : a ≠ 0) (w y : ι → ℝ) :
    weightedMean (fun i => a * w i) y = weightedMean w y := by
  simp only [weightedMean, mul_assoc, ← Finset.mul_sum]
  exact mul_div_mul_left _ _ ha

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {w : ι → ℝ} {Y : ι → Ω → ℝ}

omit [IsProbabilityMeasure P] in
/-- **The weighted mean of outcomes with a common mean is unbiased**: if `E[Yᵢ] = θ` for every
`i`, the integrable outcomes give `E[∑ᵢ wᵢ Yᵢ / ∑ᵢ wᵢ] = θ` for a nonzero total weight. -/
theorem integral_weightedMean (hw : ∑ i, w i ≠ 0) (hY : ∀ i, Integrable (Y i) P) {θ : ℝ}
    (hmean : ∀ i, ∫ ω, Y i ω ∂P = θ) :
    ∫ ω, weightedMean w (fun i => Y i ω) ∂P = θ := by
  simp only [weightedMean]
  rw [integral_div, integral_finsetSum _ fun i _ => (hY i).const_mul _]
  simp only [integral_const_mul, hmean, ← Finset.sum_mul]
  field_simp

/-- **The variance of a weighted mean** (Kish). Let the outcomes `Y₁, …, Yₙ` be square
integrable, pairwise uncorrelated, with common variance `σ²`, and let the fixed weights have a
nonzero total. Then `Var(∑ᵢ wᵢ Yᵢ / ∑ᵢ wᵢ) = σ² ∑ᵢ wᵢ² / (∑ᵢ wᵢ)² = σ² / ESS`. -/
theorem variance_weightedMean (hw : ∑ i, w i ≠ 0) (hY : ∀ i, MemLp (Y i) 2 P) {σ2 : ℝ}
    (hvar : ∀ i, Var[Y i; P] = σ2) (hcov : ∀ i j, i ≠ j → cov[Y i, Y j; P] = 0) :
    Var[fun ω => weightedMean w (fun i => Y i ω); P] =
        σ2 * (∑ i, w i ^ 2) / (∑ i, w i) ^ 2 ∧
      Var[fun ω => weightedMean w (fun i => Y i ω); P] = σ2 / ess w := by
  classical
  set S := ∑ i, w i with hS
  have hest : (fun ω => weightedMean w (fun i => Y i ω)) = fun ω => ∑ i, (w i / S) * Y i ω := by
    funext ω
    rw [weightedMean, Finset.sum_div]
    exact Finset.sum_congr rfl fun i _ => by ring
  have hX : ∀ i, MemLp (fun ω => (w i / S) * Y i ω) 2 P := fun i => (hY i).const_mul _
  have hv : Var[fun ω => weightedMean w (fun i => Y i ω); P] = σ2 * (∑ i, w i ^ 2) / S ^ 2 := by
    rw [hest, variance_fun_sum hX]
    have hterm : ∀ i j, cov[fun ω => (w i / S) * Y i ω, fun ω => (w j / S) * Y j ω; P] =
        if i = j then (w i / S) ^ 2 * σ2 else 0 := by
      intro i j
      rw [covariance_const_mul_left, covariance_const_mul_right]
      split_ifs with h
      · subst h
        rw [covariance_self (hY i).aestronglyMeasurable.aemeasurable, hvar]
        ring
      · rw [hcov i j h]
        ring
    simp only [hterm, Finset.sum_ite_eq, mem_univ, ite_true]
    rw [Finset.mul_sum, Finset.sum_div]
    exact Finset.sum_congr rfl fun i _ => by field_simp
  refine ⟨hv, ?_⟩
  rw [hv, ess]
  have h2 := (sum_sq_pos_of_sum_ne_zero hw).ne'
  rw [← hS]
  field_simp

/-- **The variance inflation of a weighted mean.** Under the hypotheses of
`variance_weightedMean` with `σ² > 0`, the ratio of the variance of the weighted mean to the
variance `σ² / n` of the unweighted mean is `n / ESS`, at least one, and equal to one exactly when
the weights are equal. -/
theorem variance_weightedMean_div (hw : ∑ i, w i ≠ 0) (hY : ∀ i, MemLp (Y i) 2 P) {σ2 : ℝ}
    (hσ : 0 < σ2) (hvar : ∀ i, Var[Y i; P] = σ2)
    (hcov : ∀ i j, i ≠ j → cov[Y i, Y j; P] = 0) :
    Var[fun ω => weightedMean w (fun i => Y i ω); P] / (σ2 / Fintype.card ι) =
        Fintype.card ι / ess w ∧
      1 ≤ Var[fun ω => weightedMean w (fun i => Y i ω); P] / (σ2 / Fintype.card ι) ∧
      (Var[fun ω => weightedMean w (fun i => Y i ω); P] / (σ2 / Fintype.card ι) = 1 ↔
        ∀ i j, w i = w j) := by
  have hcard : (0 : ℝ) < Fintype.card ι := by
    have : Nonempty ι := by
      by_contra h
      rw [not_nonempty_iff] at h
      exact hw (by simp)
    exact_mod_cast Fintype.card_pos
  have he := ess_pos hw
  have hratio : Var[fun ω => weightedMean w (fun i => Y i ω); P] / (σ2 / Fintype.card ι) =
      Fintype.card ι / ess w := by
    rw [(variance_weightedMean hw hY hvar hcov).2]
    field_simp
  rw [hratio]
  exact ⟨rfl, one_le_card_div_ess hw, card_div_ess_eq_one_iff hw⟩

/-- **An instance of the variance of a weighted mean.** Under two independent fair signs
`Y₀, Y₁ ∈ {-1, 1}` (mean `0`, variance `1`, uncorrelated), the weights `(1, 2)` have effective
sample size `9/5`; the weighted mean is unbiased for `0`, has variance `5/9 = 1 / ESS`, and its
variance inflation is `2 / (9/5) = 10/9`. -/
theorem variance_weightedMean_example :
    let Y : Fin 2 → Bool × Bool → ℝ := ![fun z => signVal z.1, fun z => signVal z.2]
    let w : Fin 2 → ℝ := ![1, 2]
    ess w = 9 / 5 ∧ ∫ z, weightedMean w (fun i => Y i z) ∂uniformPairLaw = 0 ∧
      Var[fun z => weightedMean w (fun i => Y i z); uniformPairLaw] = 5 / 9 ∧
      Var[fun z => weightedMean w (fun i => Y i z); uniformPairLaw] / (1 / 2) = 10 / 9 := by
  intro Y w
  have hw : ∑ i, w i ≠ 0 := by simp [w, Fin.sum_univ_two]; norm_num
  have hY : ∀ i, MemLp (Y i) 2 uniformPairLaw := fun i => memLp_uniformPairLaw _
  have hE : ∀ i, ∫ z, Y i z ∂uniformPairLaw = 0 := by
    intro i; fin_cases i <;> (rw [integral_uniformPairLaw]; norm_num [Y, signVal])
  have hV : ∀ i, Var[Y i; uniformPairLaw] = 1 := by
    intro i
    rw [variance_eq_integral (measurable_of_finite _).aemeasurable, hE i,
      integral_uniformPairLaw]
    fin_cases i <;> norm_num [Y, signVal]
  have hind : IndepFun (Y 0) (Y 1) uniformPairLaw :=
    indepFun_prod (X := fun v => signVal v) (Y := fun v => signVal v)
      (measurable_of_finite _) (measurable_of_finite _)
  have hcov : ∀ i j, i ≠ j → cov[Y i, Y j; uniformPairLaw] = 0 := by
    intro i j hij
    fin_cases i <;> fin_cases j
    · exact absurd rfl hij
    · exact hind.covariance_eq_zero (hY 0) (hY 1)
    · rw [covariance_comm]; exact hind.covariance_eq_zero (hY 0) (hY 1)
    · exact absurd rfl hij
  have hess : ess w = 9 / 5 := by
    simp [ess, w, Fin.sum_univ_two]; norm_num
  have hvar := (variance_weightedMean hw hY hV hcov).2
  refine ⟨hess, integral_weightedMean hw (fun i => (hY i).integrable one_le_two) hE, ?_, ?_⟩
  · rw [hvar, hess]; norm_num
  · rw [hvar, hess]; norm_num

end Variance

end PopulationAdjustment

end CausalInference
