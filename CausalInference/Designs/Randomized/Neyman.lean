/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.Designs.Randomized.Complete
public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Data.Fin.VecNotation

/-!
# Neyman's variance formula for complete randomization

For the difference in means `τ̂` under complete randomization with `n1` treated and `n0`
control units out of `N = n1 + n0`, Neyman (1923) showed
`Var(τ̂) = S1²/n1 + S0²/n0 - S_τ²/N`, where `S1²`, `S0²`, `S_τ²` are the finite-population
variances (with denominator `N - 1`) of the treated potential outcomes, the control potential
outcomes, and the unit-level effects. Consequently the conservative variance `S1²/n1 + S0²/n0`
is an upper bound, attained exactly when the unit-level effects are constant. The within-arm
sample variances `s1²`, `s0²` are unbiased for `S1²`, `S0²`, so the observable estimator
`V̂ = s1²/n1 + s0²/n0` is conservative with bias exactly `S_τ²/N`. All variances with
denominator `N - 1` are used only where `1 < N`, which follows from `n1, n0 > 0`. Sources:
Neyman (1923, translated 1990); Imbens and Rubin (2015), *Causal Inference for Statistics,
Social, and Biomedical Sciences*.

## Main definitions

* `armSampleVar`: the sample variance within an arm given by an indicator vector.
* `PotentialOutcomes.sampleVarTreated`, `PotentialOutcomes.sampleVarControl`: the within-arm
  sample variances `s1²`, `s0²`, with the realized arm counts.
* `PotentialOutcomes.neymanVarEst`: the observable estimator `s1²/n1 + s0²/n0`.

## Main results

All declarations live in the namespace `CausalInference.Randomized`.

* `popVar_eq_zero_iff`: for `1 < N`, the population variance vanishes exactly for constant
  vectors.
* `neyman_variance`: Neyman's variance formula (fixed-denominator difference in means).
* `neyman_variance_obs`: the same formula for the observed difference in means.
* `neyman_variance_le`: the conservative variance is an upper bound.
* `neyman_variance_eq_iff`: the bound is attained exactly when `S_τ² = 0`.
* `neyman_variance_eq_of_constant_effect`: equality under constant effects.
* `neyman_variance_eq_iff_constant_effect`: equality holds exactly under constant effects.
* `Design.expect_armSampleVar`: a within-arm sample variance is unbiased for the population
  variance under any design with the moments of complete randomization.
* `complete_sampleVarTreated_unbiased`, `complete_sampleVarControl_unbiased`: `E[s1²] = S1²`
  for `2 ≤ n1` and `E[s0²] = S0²` for `2 ≤ n0`.
* `complete_neymanVarEst_expect`, `complete_neymanVarEst_bias`: `E[V̂] = S1²/n1 + S0²/n0` and
  `E[V̂] - Var(τ̂) = S_τ²/N`.
* `fourUnit_variance` and companions: a concrete population with `N = 4` and
  `n1 = 2`, where the variance of the difference in means is `7/2`;
  `fourUnit_expect_direct` and `fourUnit_variance_direct` check the mean `2` and the variance
  `7/2` by enumerating the six assignments.
-/

@[expose] public section

namespace CausalInference.Randomized

open Finset

variable {ι : Type*} [Fintype ι]

/-- The sum of squared deviations from the mean: `Σ_i (f i - f̄)^2 = Σ_i f i ^2 - (Σ_i f i)^2/N`.
-/
theorem sum_sq_sub_popMean (f : ι → ℝ) (hN : 0 < Fintype.card ι) :
    ∑ i, (f i - popMean f) ^ 2 =
      ∑ i, f i ^ 2 - (Fintype.card ι : ℝ)⁻¹ * (∑ i, f i) ^ 2 := by
  have hN' : (Fintype.card ι : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  simp only [sub_sq, sum_add_distrib, sum_sub_distrib, sum_const, card_univ, nsmul_eq_mul,
    popMean]
  rw [← sum_mul, ← mul_sum]
  field_simp
  ring

/-- In a population of at least two units, the finite-population variance vanishes exactly
when the vector is constant. -/
theorem popVar_eq_zero_iff (f : ι → ℝ) (hN : 1 < Fintype.card ι) :
    popVar f = 0 ↔ ∀ i j, f i = f j := by
  constructor
  · intro h
    have hN' : ((Fintype.card ι : ℝ) - 1)⁻¹ ≠ 0 := by
      have : (1 : ℝ) < Fintype.card ι := by exact_mod_cast hN
      exact inv_ne_zero (by linarith)
    rw [popVar, mul_eq_zero, or_iff_right hN',
      sum_eq_zero_iff_of_nonneg fun i _ => sq_nonneg _] at h
    intro i j
    have hi := h i (mem_univ _)
    have hj := h j (mem_univ _)
    rw [sq_eq_zero_iff, sub_eq_zero] at hi hj
    rw [hi, hj]
  · intro h
    obtain ⟨i0⟩ := Fintype.card_pos_iff.mp (by omega : 0 < Fintype.card ι)
    exact popVar_const (f i0) f (fun i => h i i0) hN

/-- A double sum whose coefficient depends only on whether the indices agree:
`Σ_i Σ_j (A if i = j else B) w_i w_j = (A - B) Σ_i w_i^2 + B (Σ_i w_i)^2`. -/
theorem sum_sum_ite_eq [DecidableEq ι] (A B : ℝ) (w : ι → ℝ) :
    ∑ i, ∑ j, (if i = j then A else B) * w i * w j =
      (A - B) * ∑ i, w i ^ 2 + B * (∑ i, w i) ^ 2 := by
  have : ∀ i j, (if i = j then A else B) * w i * w j =
      B * (w i * w j) + if i = j then (A - B) * w i ^ 2 else 0 := by
    intro i j
    split_ifs with h
    · subst h; ring
    · ring
  simp only [this, sum_add_distrib, sum_ite_eq, mem_univ, ite_true, ← mul_sum, sq,
    sum_mul_sum]
  ring

/-- The difference in means is affine in the treatment indicators:
`τ̂ = -(1/n0) Σ_i y0 i + Σ_i A_i (y1 i / n1 + y0 i / n0)`. -/
theorem PotentialOutcomes.diffInMeans_eq_linear (po : PotentialOutcomes ι) (n1 n0 : ℕ)
    (a : ι → Bool) :
    po.diffInMeans n1 n0 a = -((n0 : ℝ)⁻¹ * ∑ i, po.y0 i) +
      ∑ i, treatInd a i * (po.y1 i / n1 + po.y0 i / n0) := by
  have h1 : ∀ i, treatInd a i * po.observed a i = treatInd a i * po.y1 i := by
    intro i; unfold treatInd observed; split_ifs <;> simp
  have h0 : ∀ i, (1 - treatInd a i) * po.observed a i = (1 - treatInd a i) * po.y0 i := by
    intro i; unfold treatInd observed; split_ifs <;> simp
  simp only [diffInMeans, h1, h0, mul_sum, ← sum_neg_distrib, ← sum_sub_distrib,
    ← sum_add_distrib]
  refine sum_congr rfl fun i _ => ?_
  ring

/-- **Neyman's variance formula.** Under complete randomization with `n1` treated and `n0`
control units, `N = n1 + n0`, `n1, n0 > 0`, the variance of the difference in means over the
randomization distribution is `S1²/n1 + S0²/n0 - S_τ²/N`. The hypotheses give `1 < N`, so
every `N - 1` denominator is positive. -/
theorem neyman_variance [DecidableEq ι] (po : PotentialOutcomes ι) {n1 n0 : ℕ}
    (hn : n1 + n0 = Fintype.card ι) (hn1 : 0 < n1) (hn0 : 0 < n0) :
    (completeDesign n1 (by omega)).variance (po.diffInMeans n1 n0) =
      po.varTreated / n1 + po.varControl / n0 - po.varEffect / Fintype.card ι := by
  set d := completeDesign (ι := ι) n1 (by omega)
  set w : ι → ℝ := fun i => po.y1 i / n1 + po.y0 i / n0 with hw
  have hN1 : 1 < Fintype.card ι := by omega
  have hNr : (Fintype.card ι : ℝ) = n1 + n0 := by rw [← hn]; push_cast; ring
  have hn1r : (n1 : ℝ) ≠ 0 := by exact_mod_cast hn1.ne'
  have hn0r : (n0 : ℝ) ≠ 0 := by exact_mod_cast hn0.ne'
  have hpos1 : (0 : ℝ) < n1 := by exact_mod_cast hn1
  have hpos0 : (0 : ℝ) < n0 := by exact_mod_cast hn0
  have hNm1 : (n1 : ℝ) + n0 - 1 ≠ 0 := by
    have : (1 : ℝ) ≤ n0 := by exact_mod_cast hn0
    linarith
  -- Step 1: the general variance formula for an affine statistic.
  rw [d.variance_of_linear _ _ w fun a _ => po.diffInMeans_eq_linear n1 n0 a]
  -- Step 2: the covariances of the treatment indicators under complete randomization.
  set π : ℝ := n1 / Fintype.card ι
  set q : ℝ := n1 * (n1 - 1) / (Fintype.card ι * (Fintype.card ι - 1))
  have hcov : ∀ i j, (d.pairInclusionProb i j - d.inclusionProb i * d.inclusionProb j) * w i *
      w j = (if i = j then π - π * π else q - π * π) * w i * w j := by
    intro i j
    have hπ : ∀ k, d.inclusionProb k = π := fun k =>
      completeDesign_inclusionProb n1 (by omega) (by omega) k
    split_ifs with h
    · subst h
      rw [d.pairInclusionProb_self, hπ]
    · rw [completeDesign_pairInclusionProb n1 (by omega) hN1 h, hπ, hπ]
  simp only [hcov]
  rw [sum_sum_ite_eq]
  -- Step 3: rewrite in terms of the sum of squared deviations of `w`.
  have hsq := sum_sq_sub_popMean w (by omega)
  have hstep : (π - π * π - (q - π * π)) * ∑ i, w i ^ 2 + (q - π * π) * (∑ i, w i) ^ 2 =
      n1 * n0 / ((n1 + n0) * (n1 + n0 - 1)) * ∑ i, (w i - popMean w) ^ 2 := by
    rw [hsq]
    simp only [π, q, hNr]
    field_simp
    ring
  rw [hstep]
  -- Step 4: a unitwise identity between deviations.
  have hmw : popMean w = popMean po.y1 / n1 + popMean po.y0 / n0 := by
    simp only [popMean, hw, sum_add_distrib, ← sum_div]
    ring
  have hmt : popMean po.unitEffect = popMean po.y1 - popMean po.y0 := by
    simp only [popMean, PotentialOutcomes.unitEffect, sum_sub_distrib]
    ring
  simp only [PotentialOutcomes.varTreated, PotentialOutcomes.varControl,
    PotentialOutcomes.varEffect, popVar, hmw, hmt, hNr, mul_sum, sum_div, ← sum_add_distrib,
    ← sum_sub_distrib]
  refine sum_congr rfl fun i _ => ?_
  simp only [hw, PotentialOutcomes.unitEffect]
  field_simp
  ring

/-- **The conservative variance bound.** Under complete randomization the variance of the
difference in means is at most `S1²/n1 + S0²/n0`. -/
theorem neyman_variance_le [DecidableEq ι] (po : PotentialOutcomes ι) {n1 n0 : ℕ}
    (hn : n1 + n0 = Fintype.card ι) (hn1 : 0 < n1) (hn0 : 0 < n0) :
    (completeDesign n1 (by omega)).variance (po.diffInMeans n1 n0) ≤
      po.varTreated / n1 + po.varControl / n0 := by
  rw [neyman_variance po hn hn1 hn0]
  have h1 : 0 ≤ po.varEffect := popVar_nonneg _ (by omega)
  have h2 : 0 ≤ po.varEffect / Fintype.card ι := div_nonneg h1 (Nat.cast_nonneg _)
  linarith

/-- The conservative variance `S1²/n1 + S0²/n0` equals the true variance of the difference in
means exactly when the unit-level effects have zero finite-population variance. -/
theorem neyman_variance_eq_iff [DecidableEq ι] (po : PotentialOutcomes ι) {n1 n0 : ℕ}
    (hn : n1 + n0 = Fintype.card ι) (hn1 : 0 < n1) (hn0 : 0 < n0) :
    (completeDesign n1 (by omega)).variance (po.diffInMeans n1 n0) =
      po.varTreated / n1 + po.varControl / n0 ↔ po.varEffect = 0 := by
  rw [neyman_variance po hn hn1 hn0]
  have hN : (Fintype.card ι : ℝ) ≠ 0 := by
    have : 0 < Fintype.card ι := by omega
    exact_mod_cast this.ne'
  constructor
  · intro h
    have : po.varEffect / Fintype.card ι = 0 := by linarith
    simpa [hN] using this
  · intro h
    simp [h]

/-- **Equality under constant effects.** If every unit has the same treatment effect, the
variance of the difference in means under complete randomization equals the conservative
variance `S1²/n1 + S0²/n0`. -/
theorem neyman_variance_eq_of_constant_effect [DecidableEq ι] (po : PotentialOutcomes ι)
    {n1 n0 : ℕ} (hn : n1 + n0 = Fintype.card ι) (hn1 : 0 < n1) (hn0 : 0 < n0) (c : ℝ)
    (hc : ∀ i, po.unitEffect i = c) :
    (completeDesign n1 (by omega)).variance (po.diffInMeans n1 n0) =
      po.varTreated / n1 + po.varControl / n0 :=
  (neyman_variance_eq_iff po hn hn1 hn0).mpr (popVar_const c _ hc (by omega))

/-- **Equality forces a constant effect.** Under complete randomization with `n1, n0 > 0`, the
variance of the difference in means equals the conservative variance `S1²/n1 + S0²/n0` if and
only if every unit has the same treatment effect. -/
theorem neyman_variance_eq_iff_constant_effect [DecidableEq ι] (po : PotentialOutcomes ι)
    {n1 n0 : ℕ} (hn : n1 + n0 = Fintype.card ι) (hn1 : 0 < n1) (hn0 : 0 < n0) :
    (completeDesign n1 (by omega)).variance (po.diffInMeans n1 n0) =
      po.varTreated / n1 + po.varControl / n0 ↔ ∃ c, ∀ i, po.unitEffect i = c := by
  rw [neyman_variance_eq_iff po hn hn1 hn0, PotentialOutcomes.varEffect,
    popVar_eq_zero_iff _ (by omega)]
  constructor
  · intro h
    obtain ⟨i0⟩ := Fintype.card_pos_iff.mp (by omega : 0 < Fintype.card ι)
    exact ⟨po.unitEffect i0, fun i => h i i0⟩
  · rintro ⟨c, hc⟩ i j
    rw [hc i, hc j]

/-! ### The observed difference in means -/

/-- **Neyman's variance formula for the observed difference in means.** Under complete
randomization with `n1` treated and `n0` control units, `N = n1 + n0`, `n1, n0 > 0`, the
variance of the observed difference in means (realized arm counts as denominators) is
`S1²/n1 + S0²/n0 - S_τ²/N`. -/
theorem neyman_variance_obs [DecidableEq ι] (po : PotentialOutcomes ι) {n1 n0 : ℕ}
    (hn : n1 + n0 = Fintype.card ι) (hn1 : 0 < n1) (hn0 : 0 < n0) :
    (completeDesign n1 (by omega)).variance po.diffInMeansObs =
      po.varTreated / n1 + po.varControl / n0 - po.varEffect / Fintype.card ι := by
  rw [Design.variance_congr _ fun a ha => po.diffInMeansObs_eq_diffInMeans hn ha]
  exact neyman_variance po hn hn1 hn0

/-! ### The observable variance estimator -/

/-- The sample variance within an arm: for an arm indicator vector `B` (entries `0` or `1`) of
size `m` and outcomes `y`, `(m - 1)⁻¹ Σ_i B_i (y_i - ȳ_B)^2` with `ȳ_B = m⁻¹ Σ_j B_j y_j`. It is
a sample variance when `2 ≤ m`. -/
noncomputable def armSampleVar (B : ι → ℝ) (m : ℝ) (y : ι → ℝ) : ℝ :=
  (m - 1)⁻¹ * ∑ i, B i * (y i - m⁻¹ * ∑ j, B j * y j) ^ 2

/-- The arm sample variance only reads the outcomes of units in the arm. -/
theorem armSampleVar_congr (B : ι → ℝ) (m : ℝ) {y y' : ι → ℝ}
    (h : ∀ i, B i ≠ 0 → y i = y' i) : armSampleVar B m y = armSampleVar B m y' := by
  have hpt : ∀ i, B i * y i = B i * y' i := fun i => by
    by_cases hB : B i = 0
    · simp [hB]
    · rw [h i hB]
  unfold armSampleVar
  simp only [hpt]
  congr 1
  refine sum_congr rfl fun i _ => ?_
  by_cases hB : B i = 0
  · simp [hB]
  · rw [h i hB]

/-- The within-arm sum of squared deviations: if `Σ_i B_i = m ≠ 0`, then
`Σ_i B_i (y_i - ȳ_B)^2 = Σ_i B_i y_i^2 - m⁻¹ (Σ_i B_i y_i)^2`. -/
theorem sum_mul_sq_sub_armMean (B y : ι → ℝ) (m : ℝ) (hm : ∑ i, B i = m) (hm0 : m ≠ 0) :
    ∑ i, B i * (y i - m⁻¹ * ∑ j, B j * y j) ^ 2 =
      ∑ i, B i * y i ^ 2 - m⁻¹ * (∑ i, B i * y i) ^ 2 := by
  set S := ∑ j, B j * y j
  have : ∀ i, B i * (y i - m⁻¹ * S) ^ 2 =
      B i * y i ^ 2 - 2 * (m⁻¹ * S) * (B i * y i) + (m⁻¹ * S) ^ 2 * B i := fun i => by ring
  simp only [this, sum_add_distrib, sum_sub_distrib, ← mul_sum, hm]
  field_simp
  ring

/-- **Unbiasedness of a within-arm sample variance.** Let `B a` be an arm indicator vector
(entries `0` or `1`) that has exactly `m` ones for every assignment of the support, with
first moments `E[B_i] = m / N` and, for `i ≠ j`, second moments
`E[B_i B_j] = m (m - 1) / (N (N - 1))`. If `2 ≤ m ≤ N`, the arm sample variance of a fixed
vector `y` is unbiased for its finite-population variance. -/
theorem Design.expect_armSampleVar (d : Design ι) (B : (ι → Bool) → ι → ℝ)
    (m : ℕ) (y : ι → ℝ) (hB : ∀ a i, B a i * B a i = B a i)
    (hsum : ∀ a ∈ d.support, ∑ i, B a i = m)
    (h1 : ∀ i, d.expect (fun a => B a i) = m / Fintype.card ι)
    (h2 : ∀ i j, i ≠ j → d.expect (fun a => B a i * B a j) =
      m * (m - 1) / (Fintype.card ι * (Fintype.card ι - 1)))
    (hm : 2 ≤ m) (hmN : m ≤ Fintype.card ι) :
    d.expect (fun a => armSampleVar (B a) m y) = popVar y := by
  classical
  have hN : 0 < Fintype.card ι := by omega
  have hNr : (2 : ℝ) ≤ Fintype.card ι := by exact_mod_cast (by omega : 2 ≤ Fintype.card ι)
  have hmr : (2 : ℝ) ≤ m := by exact_mod_cast hm
  have hm0 : (m : ℝ) ≠ 0 := by linarith
  have hm1 : (m : ℝ) - 1 ≠ 0 := by linarith
  have hN0 : (Fintype.card ι : ℝ) ≠ 0 := by linarith
  have hN1 : (Fintype.card ι : ℝ) - 1 ≠ 0 := by linarith
  set π : ℝ := m / Fintype.card ι
  set q : ℝ := m * (m - 1) / (Fintype.card ι * (Fintype.card ι - 1))
  rw [d.expect_congr (g := fun a => ((m : ℝ) - 1)⁻¹ * (∑ i, y i ^ 2 * B a i -
      (m : ℝ)⁻¹ * ∑ i, ∑ j, y i * y j * (B a i * B a j))) fun a ha => by
    rw [armSampleVar, sum_mul_sq_sub_armMean _ _ _ (hsum a ha) hm0, sq, sum_mul_sum]
    congr 2
    · exact sum_congr rfl fun i _ => by ring
    · congr 1
      exact sum_congr rfl fun i _ => sum_congr rfl fun j _ => by ring]
  have e1 : ∀ i, d.expect (fun a => y i ^ 2 * B a i) = π * y i ^ 2 := fun i => by
    rw [d.expect_mul_left, h1]
    ring
  have e2 : ∀ i j, d.expect (fun a => y i * y j * (B a i * B a j)) =
      (if i = j then π else q) * y i * y j := fun i j => by
    rw [d.expect_mul_left]
    split_ifs with h
    · subst h
      rw [d.expect_congr (g := fun a => B a i) (fun a _ => hB a i), h1]
      ring
    · rw [h2 i j h]
      ring
  rw [d.expect_mul_left, d.expect_sub, d.expect_sum, d.expect_mul_left, d.expect_sum]
  simp only [e1, d.expect_sum, e2]
  rw [sum_sum_ite_eq, ← mul_sum, popVar, sum_sq_sub_popMean y hN]
  simp only [π, q]
  field_simp
  ring

/-- The within-arm sample variance of the treated units, `s1²`, with the realized number of
treated units as arm size. It is a sample variance only when at least two units are treated. -/
noncomputable def PotentialOutcomes.sampleVarTreated (po : PotentialOutcomes ι)
    (a : ι → Bool) : ℝ :=
  armSampleVar (treatInd a) (numTreated a) (po.observed a)

/-- The within-arm sample variance of the control units, `s0²`, with the realized number of
control units as arm size. It is a sample variance only when at least two units are controls.
-/
noncomputable def PotentialOutcomes.sampleVarControl (po : PotentialOutcomes ι)
    (a : ι → Bool) : ℝ :=
  armSampleVar (fun i => 1 - treatInd a i) ((Fintype.card ι - numTreated a : ℕ) : ℝ)
    (po.observed a)

/-- Neyman's observable variance estimator `V̂ = s1²/n1 + s0²/n0` for the difference in means,
with the realized arm counts. It is meaningful only when each arm has at least two units. -/
noncomputable def PotentialOutcomes.neymanVarEst (po : PotentialOutcomes ι) (a : ι → Bool) : ℝ :=
  po.sampleVarTreated a / numTreated a +
    po.sampleVarControl a / ((Fintype.card ι - numTreated a : ℕ) : ℝ)

/-- **Unbiasedness of the treated sample variance.** Under complete randomization with
`2 ≤ n1 ≤ N` treated units, `E[s1²] = S1²`. -/
theorem complete_sampleVarTreated_unbiased [DecidableEq ι] (po : PotentialOutcomes ι)
    {n1 : ℕ} (h : n1 ≤ Fintype.card ι) (hn1 : 2 ≤ n1) :
    (completeDesign n1 h).expect po.sampleVarTreated = po.varTreated := by
  set d := completeDesign (ι := ι) n1 h
  have hN1 : 1 < Fintype.card ι := by omega
  rw [d.expect_congr (g := fun a => armSampleVar (treatInd a) n1 po.y1) fun a ha => by
    rw [PotentialOutcomes.sampleVarTreated, mem_completeSupport.mp ha]
    refine armSampleVar_congr _ _ fun i hi => ?_
    simp only [treatInd, ne_eq, ite_eq_right_iff, Classical.not_imp] at hi
    simp [PotentialOutcomes.observed, hi.1]]
  refine d.expect_armSampleVar (fun a i => treatInd a i) n1 po.y1
    (fun a i => by unfold treatInd; split_ifs <;> norm_num)
    (fun a ha => by rw [← numTreated_eq_sum, mem_completeSupport.mp ha])
    (fun i => completeDesign_inclusionProb n1 h (by omega) i)
    (fun i j hij => completeDesign_pairInclusionProb n1 h hN1 hij) hn1 h

/-- **Unbiasedness of the control sample variance.** Under complete randomization with `n1`
treated and `n0` control units, `n1 + n0 = N`, `2 ≤ n0`, `E[s0²] = S0²`. -/
theorem complete_sampleVarControl_unbiased [DecidableEq ι] (po : PotentialOutcomes ι)
    {n1 n0 : ℕ} (hn : n1 + n0 = Fintype.card ι) (hn0 : 2 ≤ n0) :
    (completeDesign n1 (by omega)).expect po.sampleVarControl = po.varControl := by
  set d := completeDesign (ι := ι) n1 (by omega)
  have hN1 : 1 < Fintype.card ι := by omega
  have hNr : (Fintype.card ι : ℝ) = n1 + n0 := by rw [← hn]; push_cast; ring
  have h20 : (2 : ℝ) ≤ n0 := by exact_mod_cast hn0
  have h10 : (0 : ℝ) ≤ n1 := Nat.cast_nonneg _
  have hN0 : (n1 : ℝ) + n0 ≠ 0 := by linarith
  have hNm : (n1 : ℝ) + n0 - 1 ≠ 0 := by linarith
  have hπ : ∀ i, d.inclusionProb i = n1 / Fintype.card ι :=
    fun i => completeDesign_inclusionProb n1 _ (by omega) i
  rw [d.expect_congr (g := fun a => armSampleVar (fun i => 1 - treatInd a i) n0 po.y0)
    fun a ha => by
      have h0 : Fintype.card ι - numTreated a = n0 := by
        rw [mem_completeSupport.mp ha]; omega
      rw [PotentialOutcomes.sampleVarControl, h0]
      refine armSampleVar_congr _ _ fun i hi => ?_
      cases hai : a i
      · simp [PotentialOutcomes.observed, hai]
      · simp [treatInd, hai] at hi]
  refine d.expect_armSampleVar (fun a i => 1 - treatInd a i) n0 po.y0
    (fun a i => by unfold treatInd; split_ifs <;> norm_num) (fun a ha => ?_) (fun i => ?_)
    (fun i j hij => ?_) hn0 (by omega)
  · rw [sum_sub_distrib, ← numTreated_eq_sum, mem_completeSupport.mp ha]
    simp [hNr]
  · rw [d.expect_sub, d.expect_const]
    change 1 - d.inclusionProb i = _
    rw [hπ, hNr]
    field_simp
    ring
  · rw [d.expect_congr (g := fun a => treatInd a i * treatInd a j - treatInd a i -
      treatInd a j + 1) (fun _ _ => by ring), d.expect_add, d.expect_sub, d.expect_sub,
      d.expect_const]
    change d.pairInclusionProb i j - d.inclusionProb i - d.inclusionProb j + 1 = _
    rw [completeDesign_pairInclusionProb n1 _ hN1 hij, hπ, hπ, hNr]
    field_simp
    ring

/-- **Expectation of Neyman's variance estimator.** Under complete randomization with `n1`
treated and `n0` control units, `n1 + n0 = N`, `2 ≤ n1`, `2 ≤ n0`, the observable estimator
`V̂ = s1²/n1 + s0²/n0` has expectation `S1²/n1 + S0²/n0`. -/
theorem complete_neymanVarEst_expect [DecidableEq ι] (po : PotentialOutcomes ι) {n1 n0 : ℕ}
    (hn : n1 + n0 = Fintype.card ι) (hn1 : 2 ≤ n1) (hn0 : 2 ≤ n0) :
    (completeDesign n1 (by omega)).expect po.neymanVarEst =
      po.varTreated / n1 + po.varControl / n0 := by
  set d := completeDesign (ι := ι) n1 (by omega)
  rw [d.expect_congr (g := fun a => (n1 : ℝ)⁻¹ * po.sampleVarTreated a +
      (n0 : ℝ)⁻¹ * po.sampleVarControl a) fun a ha => by
    have h0 : Fintype.card ι - numTreated a = n0 := by rw [mem_completeSupport.mp ha]; omega
    rw [PotentialOutcomes.neymanVarEst, h0, mem_completeSupport.mp ha]
    ring,
    d.expect_add, d.expect_mul_left, d.expect_mul_left,
    complete_sampleVarTreated_unbiased po _ hn1, complete_sampleVarControl_unbiased po hn hn0]
  ring

/-- **Conservativeness of Neyman's variance estimator.** Under complete randomization with
`n1` treated and `n0` control units, `n1 + n0 = N`, `2 ≤ n1`, `2 ≤ n0`, the bias of the
observable estimator `V̂ = s1²/n1 + s0²/n0` for the variance of the observed difference in
means is exactly `S_τ²/N`: `E[V̂] - Var(τ̂) = S_τ²/N ≥ 0`. -/
theorem complete_neymanVarEst_bias [DecidableEq ι] (po : PotentialOutcomes ι) {n1 n0 : ℕ}
    (hn : n1 + n0 = Fintype.card ι) (hn1 : 2 ≤ n1) (hn0 : 2 ≤ n0) :
    (completeDesign n1 (by omega)).expect po.neymanVarEst -
      (completeDesign n1 (by omega)).variance po.diffInMeansObs =
      po.varEffect / Fintype.card ι := by
  rw [complete_neymanVarEst_expect po hn hn1 hn0, neyman_variance_obs po hn (by omega) (by omega)]
  ring

/-! ### A concrete example: `N = 4`, `n1 = 2` -/

section Example

/-- Potential outcomes of four units: `y1 = (3, 5, 4, 8)` and `y0 = (1, 2, 4, 5)`, so the unit
effects are `(2, 3, 0, 3)`. -/
def fourUnitPO : PotentialOutcomes (Fin 4) where
  y1 := ![3, 5, 4, 8]
  y0 := ![1, 2, 4, 5]

/-- There are `6 = 4 choose 2` assignments treating two of four units. -/
theorem fourUnit_card : #(completeSupport (ι := Fin 4) 2) = 6 := by decide

/-- Each of four units is treated with probability `1/2` when two are treated. -/
theorem fourUnit_inclusionProb (i : Fin 4) :
    (completeDesign (ι := Fin 4) 2 (by decide)).inclusionProb i = 1 / 2 := by
  rw [completeDesign_inclusionProb 2 _ (by decide)]
  norm_num

/-- Two distinct units out of four are both treated with probability `1/6`. -/
theorem fourUnit_pairInclusionProb :
    (completeDesign (ι := Fin 4) 2 (by decide)).pairInclusionProb 0 1 = 1 / 6 := by
  rw [completeDesign_pairInclusionProb 2 _ (by decide) (by decide)]
  norm_num

/-- The average treatment effect of the example is `2`. -/
theorem fourUnit_ate : fourUnitPO.ate = 2 := by
  simp [PotentialOutcomes.ate, popMean, PotentialOutcomes.unitEffect, fourUnitPO,
    Fin.sum_univ_four]
  norm_num

/-- In the example `S1² = 14/3`, `S0² = 10/3`, `S_τ² = 2`, so Neyman's formula gives the variance
`(14/3)/2 + (10/3)/2 - 2/4 = 7/2` for the difference in means. -/
theorem fourUnit_variance :
    (completeDesign (ι := Fin 4) 2 (by decide)).variance (fourUnitPO.diffInMeans 2 2) = 7 / 2 := by
  rw [neyman_variance fourUnitPO (by decide) (by decide) (by decide)]
  simp [PotentialOutcomes.varTreated, PotentialOutcomes.varControl,
    PotentialOutcomes.varEffect, popVar, popMean, PotentialOutcomes.unitEffect, fourUnitPO,
    Fin.sum_univ_four]
  norm_num

/-- The six assignments treating two of four units, listed explicitly. -/
theorem fourUnit_completeSupport : completeSupport (ι := Fin 4) 2 =
    {![true, true, false, false], ![true, false, true, false], ![true, false, false, true],
      ![false, true, true, false], ![false, true, false, true], ![false, false, true, true]} := by
  decide

/-- Direct enumeration: averaging the difference in means over the six equally likely
assignments gives `2`, the average treatment effect. The estimator takes the values
`9/2, 4, 3/2, 5/2, 0, -1/2`. This check does not use the general unbiasedness theorem. -/
theorem fourUnit_expect_direct :
    (completeDesign (ι := Fin 4) 2 (by decide)).expect (fourUnitPO.diffInMeans 2 2) = 2 := by
  simp only [completeDesign, Design.uniform_expect, fourUnit_card]
  rw [fourUnit_completeSupport, sum_insert (by decide), sum_insert (by decide),
    sum_insert (by decide), sum_insert (by decide), sum_insert (by decide), sum_singleton]
  simp [PotentialOutcomes.diffInMeans, treatInd, PotentialOutcomes.observed, fourUnitPO,
    Fin.sum_univ_four]
  norm_num

/-- Direct enumeration: the variance of the difference in means over the six equally likely
assignments is `7/2`. This check does not use Neyman's formula. -/
theorem fourUnit_variance_direct :
    (completeDesign (ι := Fin 4) 2 (by decide)).variance (fourUnitPO.diffInMeans 2 2) =
      7 / 2 := by
  rw [Design.variance, fourUnit_expect_direct]
  simp only [completeDesign, Design.uniform_expect, fourUnit_card]
  rw [fourUnit_completeSupport, sum_insert (by decide), sum_insert (by decide),
    sum_insert (by decide), sum_insert (by decide), sum_insert (by decide), sum_singleton]
  simp [PotentialOutcomes.diffInMeans, treatInd, PotentialOutcomes.observed, fourUnitPO,
    Fin.sum_univ_four]
  norm_num

end Example

end CausalInference.Randomized
