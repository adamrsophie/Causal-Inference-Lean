/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.BiasAnalysis.Distributions
public import Mathlib.Analysis.Real.Pi.Bounds
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Probability.Distributions.Gaussian.Multivariate

/-!
# Standard normal bounds, exact percentiles and the Gaussian copula

Companion to `BiasAnalysis/Distributions.lean` for Chapter 7 of Matthew P. Fox, Richard F.
MacLehose and Timothy L. Lash (2021), *Applying Quantitative Bias Analysis to Epidemiologic
Data*, second edition.

## Main results

* Certified values of the standard normal distribution function `Φ`:
  `cdf_stdNormal_eq_integral` (`Φ(x) = 1/2 + (2π)^(-1/2) ∫₀ˣ e^{-t²/2} dt` for `x ≥ 0`),
  `cdf_stdNormal_neg` (`Φ(-x) = 1 - Φ(x)`), the alternating Taylor bounds
  `expNegPartialSum_le_exp_neg` and `exp_neg_le_expNegPartialSum`, and
  `cdf_stdNormal_one_ninety_six` (`Φ(1.96) ∈ (0.975002, 0.975003)`).
* `logitNormal_percentiles_example`: for `logit(PPV) ~ N(2.94, 0.48²)` the quantiles of the
  positive predictive value at the levels exactly `0.025`, `0.5`, `0.975` lie in
  `(0.8807, 0.8808)`, `(0.9497, 0.9498)`, `(0.9797, 0.9798)`; the book prints `0.88`, `0.95`,
  `0.98`.
* The standard bivariate normal law `bivariateNormal ρ` (Mathlib's `multivariateGaussian` with
  correlation matrix `!![1, ρ; ρ, 1]`), its standard normal coordinates and covariance `ρ`, the
  Gaussian copula `gaussianCopula ρ`, and `measureReal_norta_eq_gaussianCopula`: the NORTA pair of
  Equation 7.7 has joint distribution function `C_ρ(F₁(x), F₂(y))`.

The correlation of the transformed pair is in general not `ρ`: it depends on the target laws
through the quantile transformations. `norta_correlation_ne_example` shows this for `ρ = 1`: with
a fair coin and a uniform target the transformed pair has correlation `√3/2 < 1`, and
`norta_correlation_ne_bivariateNormal_one` restates it for a pair with law `bivariateNormal 1`
(the diagonal pair `(Z, Z)` has that law by `map_diag_gaussianReal`). At the interior value
`ρ = 1/2`, `bivariateNormal_half_orthant` gives `P(Z₁ > 0, Z₂ > 0) = 1/3`, and
`norta_correlation_ne_bivariateNormal_half` shows that two fair coin targets give correlation
`1/3`, not `1/2`.
-/

@[expose] public section

namespace CausalInference

namespace BiasAnalysis

namespace Distributions

open MeasureTheory ProbabilityTheory Set

section NormalCDF

/-- The truncated series `T_n(u) = ∑_{k < n} (-u)^k / k!` of `exp(-u)`. -/
noncomputable def expNegPartialSum (n : ℕ) (u : ℝ) : ℝ :=
  ∑ k ∈ Finset.range n, (-u) ^ k / (k.factorial : ℝ)

lemma expNegPartialSum_zero_left (u : ℝ) : expNegPartialSum 0 u = 0 := by
  simp [expNegPartialSum]

lemma expNegPartialSum_succ_zero (n : ℕ) : expNegPartialSum (n + 1) 0 = 1 := by
  simp [expNegPartialSum, Finset.sum_range_succ']

/-- `T_{n+1}' = -T_n`. -/
lemma hasDerivAt_expNegPartialSum (n : ℕ) (u : ℝ) :
    HasDerivAt (expNegPartialSum (n + 1)) (-expNegPartialSum n u) u := by
  induction n with
  | zero =>
    have h : expNegPartialSum 1 = fun _ => 1 := by funext x; simp [expNegPartialSum]
    rw [h, expNegPartialSum_zero_left, neg_zero]
    exact hasDerivAt_const u 1
  | succ n ih =>
    have hfun : expNegPartialSum (n + 1 + 1) =
        fun x => expNegPartialSum (n + 1) x + (-x) ^ (n + 1) / ((n + 1).factorial : ℝ) := by
      funext x; simp only [expNegPartialSum]; rw [Finset.sum_range_succ]
    have hterm : HasDerivAt (fun x : ℝ => (-x) ^ (n + 1) / ((n + 1).factorial : ℝ))
        (-((-u) ^ n / (n.factorial : ℝ))) u := by
      have h := ((hasDerivAt_neg u).pow (n + 1)).div_const ((n + 1).factorial : ℝ)
      convert h using 1
      rw [Nat.add_sub_cancel, Nat.factorial_succ]
      push_cast
      field_simp
    rw [hfun]
    convert ih.add hterm using 1
    simp only [expNegPartialSum]
    rw [Finset.sum_range_succ]
    ring

/-- Alternating Taylor bounds: `(-1)^n (exp(-u) - T_n(u)) ≥ 0` for `u ≥ 0`. -/
lemma expNegPartialSum_alternating (n : ℕ) {u : ℝ} (hu : 0 ≤ u) :
    0 ≤ (-1) ^ n * (Real.exp (-u) - expNegPartialSum n u) := by
  induction n generalizing u with
  | zero =>
    rw [pow_zero, one_mul, expNegPartialSum_zero_left, sub_zero]
    exact (Real.exp_pos _).le
  | succ n ih =>
    set h : ℝ → ℝ := fun x => (-1) ^ (n + 1) * (Real.exp (-x) - expNegPartialSum (n + 1) x)
      with hh
    have hd : ∀ x, HasDerivAt h ((-1) ^ n * (Real.exp (-x) - expNegPartialSum n x)) x := by
      intro x
      have := ((hasDerivAt_neg x).exp.sub (hasDerivAt_expNegPartialSum n x)).const_mul
        ((-1 : ℝ) ^ (n + 1))
      convert this using 1
      ring
    have hmono : MonotoneOn h (Ici 0) :=
      monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ici 0)
        (fun x _ => (hd x).continuousAt.continuousWithinAt)
        (fun x _ => (hd x).hasDerivWithinAt) (fun x hx => ih (interior_subset hx))
    have h0 : h 0 = 0 := by
      rw [hh]; simp only [neg_zero, Real.exp_zero, expNegPartialSum_succ_zero, sub_self, mul_zero]
    have := hmono self_mem_Ici hu hu
    rwa [h0] at this

/-- Even truncations bound `exp(-u)` from below for `u ≥ 0`. -/
theorem expNegPartialSum_le_exp_neg (m : ℕ) {u : ℝ} (hu : 0 ≤ u) :
    expNegPartialSum (2 * m) u ≤ Real.exp (-u) := by
  have h := expNegPartialSum_alternating (2 * m) hu
  rw [pow_mul, neg_one_sq, one_pow, one_mul] at h
  linarith

/-- Odd truncations bound `exp(-u)` from above for `u ≥ 0`. -/
theorem exp_neg_le_expNegPartialSum (m : ℕ) {u : ℝ} (hu : 0 ≤ u) :
    Real.exp (-u) ≤ expNegPartialSum (2 * m + 1) u := by
  have h := expNegPartialSum_alternating (2 * m + 1) hu
  rw [pow_succ, pow_mul, neg_one_sq, one_pow, one_mul] at h
  linarith

/-- The polynomial `∑_{k < n} (-1/2)^k / k! · x^(2k+1)/(2k+1)`, the integral of
`T_n(t²/2)` over `[0, x]`. -/
noncomputable def gaussIntPoly (n : ℕ) (x : ℝ) : ℝ :=
  ∑ k ∈ Finset.range n, (-1 / 2 : ℝ) ^ k / (k.factorial : ℝ) * (x ^ (2 * k + 1) / (2 * k + 1))

lemma integral_expNegPartialSum (n : ℕ) (x : ℝ) :
    ∫ t in (0 : ℝ)..x, expNegPartialSum n (t ^ 2 / 2) = gaussIntPoly n x := by
  have h : (fun t : ℝ => expNegPartialSum n (t ^ 2 / 2)) =
      fun t => ∑ k ∈ Finset.range n, (-1 / 2 : ℝ) ^ k / (k.factorial : ℝ) * t ^ (2 * k) := by
    funext t
    simp only [expNegPartialSum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [pow_mul, show -(t ^ 2 / 2) = (-1 / 2) * t ^ 2 by ring, mul_pow]
    ring
  have hsum := intervalIntegral.integral_finsetSum (μ := volume) (a := 0) (b := x)
    (s := Finset.range n)
    (f := fun k (t : ℝ) => (-1 / 2 : ℝ) ^ k / (k.factorial : ℝ) * t ^ (2 * k)) fun k _ =>
      (by fun_prop : Continuous fun t : ℝ =>
        (-1 / 2 : ℝ) ^ k / (k.factorial : ℝ) * t ^ (2 * k)).intervalIntegrable (μ := volume) _ _
  rw [h, hsum]
  simp only [gaussIntPoly]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [intervalIntegral.integral_const_mul, integral_pow]
  push_cast
  ring

/-- The standard normal distribution function on `[0, ∞)`:
`Φ(x) = Φ(0) + (2π)^(-1/2) ∫₀ˣ e^{-t²/2} dt`. -/
lemma cdf_stdNormal_sub_cdf_zero {x : ℝ} (hx : 0 ≤ x) :
    cdf (gaussianReal 0 1) x - cdf (gaussianReal 0 1) 0 =
      (Real.sqrt (2 * Real.pi))⁻¹ * ∫ t in (0 : ℝ)..x, Real.exp (-(t ^ 2 / 2)) := by
  have h1 := (cdf (gaussianReal 0 1)).measure_Ioc 0 x
  rw [measure_cdf, gaussianReal_apply_eq_integral 0 one_ne_zero] at h1
  have hnn : 0 ≤ ∫ t in Ioc 0 x, gaussianPDFReal 0 1 t :=
    setIntegral_nonneg measurableSet_Ioc fun t _ => gaussianPDFReal_nonneg 0 1 t
  have hmono : 0 ≤ cdf (gaussianReal 0 1) x - cdf (gaussianReal 0 1) 0 :=
    sub_nonneg.2 ((cdf _).mono hx)
  rw [← (ENNReal.ofReal_eq_ofReal_iff hnn hmono).1 h1, ← intervalIntegral.integral_of_le hx,
    ← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_congr fun t _ => ?_
  simp only [gaussianPDFReal, NNReal.coe_one, mul_one, sub_zero]
  congr 2
  ring

/-- Symmetry of the standard normal distribution function: `Φ(-x) = 1 - Φ(x)`. -/
theorem cdf_stdNormal_neg (x : ℝ) :
    cdf (gaussianReal 0 1) (-x) = 1 - cdf (gaussianReal 0 1) x := by
  have : NullSingletonClass (gaussianReal 0 1) := nullSingletonClass_gaussianReal one_ne_zero
  have hmap : (gaussianReal 0 1).map (fun y => -y) = gaussianReal 0 1 := by
    rw [gaussianReal_map_neg, neg_zero]
  rw [cdf_eq_real, cdf_eq_real]
  have h1 : (gaussianReal 0 1).real (Iic (-x)) = (gaussianReal 0 1).real (Ici x) := by
    conv_lhs => rw [← hmap]
    rw [map_measureReal_apply measurable_neg measurableSet_Iic]
    congr 1
    ext y
    simp only [mem_preimage, mem_Iic, mem_Ici, neg_le_neg_iff]
  have h2 : (gaussianReal 0 1).real (Ici x) = (gaussianReal 0 1).real (Ioi x) :=
    measureReal_congr (Ioi_ae_eq_Ici' (measure_singleton x)).symm
  rw [h1, h2, ← compl_Iic, probReal_compl_eq_one_sub measurableSet_Iic]

/-- `Φ(0) = 1/2`. -/
theorem cdf_stdNormal_zero : cdf (gaussianReal 0 1) 0 = 1 / 2 := by
  have h := cdf_stdNormal_neg 0
  rw [neg_zero] at h
  linarith

/-- The standard normal distribution function as an integral: for `x ≥ 0`,
`Φ(x) = 1/2 + (2π)^(-1/2) ∫₀ˣ e^{-t²/2} dt`. -/
theorem cdf_stdNormal_eq_integral {x : ℝ} (hx : 0 ≤ x) :
    cdf (gaussianReal 0 1) x =
      1 / 2 + (Real.sqrt (2 * Real.pi))⁻¹ * ∫ t in (0 : ℝ)..x, Real.exp (-(t ^ 2 / 2)) := by
  rw [← cdf_stdNormal_sub_cdf_zero hx, cdf_stdNormal_zero]
  ring

/-- Polynomial bounds on `Φ` on `[0, ∞)`: for every `m`,
`1/2 + P_{2m}(x)/√(2π) ≤ Φ(x) ≤ 1/2 + P_{2m+1}(x)/√(2π)` with `P_n = gaussIntPoly n`. -/
theorem cdf_stdNormal_mem_polyBounds (m : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    1 / 2 + gaussIntPoly (2 * m) x / Real.sqrt (2 * Real.pi) ≤ cdf (gaussianReal 0 1) x ∧
      cdf (gaussianReal 0 1) x ≤ 1 / 2 + gaussIntPoly (2 * m + 1) x / Real.sqrt (2 * Real.pi) := by
  have hs : 0 < Real.sqrt (2 * Real.pi) := Real.sqrt_pos.2 (by positivity)
  have hint : IntervalIntegrable (fun t : ℝ => Real.exp (-(t ^ 2 / 2))) volume 0 x :=
    (by fun_prop : Continuous fun t : ℝ => Real.exp (-(t ^ 2 / 2))).intervalIntegrable _ _
  have hpoly : ∀ n, IntervalIntegrable (fun t : ℝ => expNegPartialSum n (t ^ 2 / 2)) volume 0 x :=
    fun n => (by unfold expNegPartialSum; fun_prop :
      Continuous fun t : ℝ => expNegPartialSum n (t ^ 2 / 2)).intervalIntegrable _ _
  have hlo := intervalIntegral.integral_mono hx (hpoly (2 * m)) hint
    fun t => expNegPartialSum_le_exp_neg m (by positivity : 0 ≤ t ^ 2 / 2)
  have hhi := intervalIntegral.integral_mono hx hint (hpoly (2 * m + 1))
    fun t => exp_neg_le_expNegPartialSum m (by positivity : 0 ≤ t ^ 2 / 2)
  rw [integral_expNegPartialSum] at hlo hhi
  rw [cdf_stdNormal_eq_integral hx, ← div_eq_inv_mul]
  exact ⟨by gcongr, by gcongr⟩

/-- `c √(2π) < p` from `c² · 2 · 3.141593 < p²`, using `π < 3.141593`. -/
lemma mul_sqrt_two_pi_lt {c p : ℝ} (hp : 0 ≤ p)
    (h : c ^ 2 * (2 * 3.141593) < p ^ 2) : c * Real.sqrt (2 * Real.pi) < p := by
  have hs : (c * Real.sqrt (2 * Real.pi)) ^ 2 = c ^ 2 * (2 * Real.pi) := by
    rw [mul_pow, Real.sq_sqrt (by positivity)]
  have hpi := Real.pi_lt_d6
  refine lt_of_pow_lt_pow_left₀ 2 hp ?_
  rw [hs]
  nlinarith [sq_nonneg c]

/-- `p < c √(2π)` from `p² < c² · 2 · 3.141592`, using `3.141592 < π`. -/
lemma lt_mul_sqrt_two_pi {c p : ℝ} (hc : 0 ≤ c) (h : p ^ 2 < c ^ 2 * (2 * 3.141592)) :
    p < c * Real.sqrt (2 * Real.pi) := by
  have hs : (c * Real.sqrt (2 * Real.pi)) ^ 2 = c ^ 2 * (2 * Real.pi) := by
    rw [mul_pow, Real.sq_sqrt (by positivity)]
  have hpi := Real.pi_gt_d6
  refine lt_of_pow_lt_pow_left₀ 2 (by positivity) ?_
  rw [hs]
  nlinarith [sq_nonneg c]

/-- Certified value of the standard normal distribution function at `1.96`:
`0.975002 < Φ(1.96) < 0.975003`. In particular `Φ(1.96) ∈ (0.9750, 0.9751)`. -/
theorem cdf_stdNormal_one_ninety_six :
    0.975002 < cdf (gaussianReal 0 1) 1.96 ∧ cdf (gaussianReal 0 1) 1.96 < 0.975003 := by
  have hs : 0 < Real.sqrt (2 * Real.pi) := Real.sqrt_pos.2 (by positivity)
  obtain ⟨hlo, -⟩ := cdf_stdNormal_mem_polyBounds 8 (by norm_num : (0 : ℝ) ≤ 1.96)
  obtain ⟨-, hhi⟩ := cdf_stdNormal_mem_polyBounds 8 (by norm_num : (0 : ℝ) ≤ 1.96)
  have p16 : (0.475002 : ℝ) * Real.sqrt (2 * Real.pi) < gaussIntPoly (2 * 8) 1.96 :=
    mul_sqrt_two_pi_lt (by norm_num [gaussIntPoly, Finset.sum_range_succ, Nat.factorial])
      (by norm_num [gaussIntPoly, Finset.sum_range_succ, Nat.factorial])
  have p17 : gaussIntPoly (2 * 8 + 1) 1.96 < (0.475003 : ℝ) * Real.sqrt (2 * Real.pi) :=
    lt_mul_sqrt_two_pi (by norm_num)
      (by norm_num [gaussIntPoly, Finset.sum_range_succ, Nat.factorial])
  constructor
  · refine lt_of_lt_of_le ?_ hlo
    have : (0.475002 : ℝ) < gaussIntPoly (2 * 8) 1.96 / Real.sqrt (2 * Real.pi) :=
      (lt_div_iff₀ hs).2 p16
    linarith
  · refine lt_of_le_of_lt hhi ?_
    have : gaussIntPoly (2 * 8 + 1) 1.96 / Real.sqrt (2 * Real.pi) < (0.475003 : ℝ) :=
      (div_lt_iff₀ hs).2 p17
    linarith

/-- `Φ(1.9599) < 0.975`, which places the exact `0.975` quantile of `N(0, 1)` in
`(1.9599, 1.96]`. -/
theorem cdf_stdNormal_one_ninety_five_ninety_nine : cdf (gaussianReal 0 1) 1.9599 < 0.975 := by
  have hs : 0 < Real.sqrt (2 * Real.pi) := Real.sqrt_pos.2 (by positivity)
  obtain ⟨-, hhi⟩ := cdf_stdNormal_mem_polyBounds 8 (by norm_num : (0 : ℝ) ≤ 1.9599)
  have p17 : gaussIntPoly (2 * 8 + 1) 1.9599 < (0.475 : ℝ) * Real.sqrt (2 * Real.pi) :=
    lt_mul_sqrt_two_pi (by norm_num)
      (by norm_num [gaussIntPoly, Finset.sum_range_succ, Nat.factorial])
  refine lt_of_le_of_lt hhi ?_
  have : gaussIntPoly (2 * 8 + 1) 1.9599 / Real.sqrt (2 * Real.pi) < (0.475 : ℝ) :=
    (div_lt_iff₀ hs).2 p17
  linarith

end NormalCDF

section Percentiles

/-- An upper bound on a normal quantile from the standard normal distribution function:
if `u ≤ Φ(z)` then the `u` quantile of `N(m, s²)` is at most `m + s z`. -/
lemma quantile_gaussianReal_le {m s : ℝ} (hs : 0 < s) {v : NNReal} (hv : (v : ℝ) = s ^ 2)
    {u z : ℝ} (hu : u ∈ Ioo (0 : ℝ) 1) (h : u ≤ cdf (gaussianReal 0 1) z) :
    quantile (gaussianReal m v) u ≤ m + s * z :=
  (quantile_le_iff hu _).2 (by rw [cdf_gaussianReal_affine m hs hv z]; exact h)

/-- A lower bound on a normal quantile: if `Φ(z) < u` then the `u` quantile of `N(m, s²)`
exceeds `m + s z`. -/
lemma lt_quantile_gaussianReal {m s : ℝ} (hs : 0 < s) {v : NNReal} (hv : (v : ℝ) = s ^ 2)
    {u z : ℝ} (hu : u ∈ Ioo (0 : ℝ) 1) (h : cdf (gaussianReal 0 1) z < u) :
    m + s * z < quantile (gaussianReal m v) u :=
  lt_of_not_ge fun h' => absurd ((quantile_le_iff hu _).1 h')
    (by rw [cdf_gaussianReal_affine m hs hv z]; exact not_le.2 h)

lemma sigmoid_bound_lo1 : 0.8807 < Real.sigmoid (2.94 + 0.48 * -1.96) := by
  refine lt_sigmoid_of_lt_exp (by norm_num) (lt_of_lt_of_le ?_
    ((show (2.94 : ℝ) + 0.48 * -1.96 = 4 * 0.4998 by norm_num) ▸
      expPartialSum_pow_le (by norm_num)))
  norm_num [expPartialSum, Finset.sum_range_succ, Nat.factorial]

lemma sigmoid_bound_hi1 : Real.sigmoid (2.94 + 0.48 * -1.9599) < 0.8808 := by
  refine sigmoid_lt_of_exp_lt (by norm_num) (lt_of_le_of_lt
    ((show (2.94 : ℝ) + 0.48 * -1.9599 = 4 * 0.499812 by norm_num) ▸
      exp_four_mul_le (by norm_num) (by norm_num)) ?_)
  norm_num [expPartialSum, Finset.sum_range_succ, Nat.factorial]

lemma sigmoid_bound_lo2 : 0.9497 < Real.sigmoid 2.94 := by
  refine lt_sigmoid_of_lt_exp (by norm_num) (lt_of_lt_of_le ?_
    ((show (2.94 : ℝ) = 4 * 0.735 by norm_num) ▸ expPartialSum_pow_le (by norm_num)))
  norm_num [expPartialSum, Finset.sum_range_succ, Nat.factorial]

lemma sigmoid_bound_hi2 : Real.sigmoid 2.94 < 0.9498 := by
  refine sigmoid_lt_of_exp_lt (by norm_num) (lt_of_le_of_lt
    ((show (2.94 : ℝ) = 4 * 0.735 by norm_num) ▸
      exp_four_mul_le (by norm_num) (by norm_num)) ?_)
  norm_num [expPartialSum, Finset.sum_range_succ, Nat.factorial]

lemma sigmoid_bound_lo3 : 0.9797 < Real.sigmoid (2.94 + 0.48 * 1.9599) := by
  refine lt_sigmoid_of_lt_exp (by norm_num) (lt_of_lt_of_le ?_
    ((show (2.94 : ℝ) + 0.48 * 1.9599 = 4 * 0.970188 by norm_num) ▸
      expPartialSum_pow_le (by norm_num)))
  norm_num [expPartialSum, Finset.sum_range_succ, Nat.factorial]

lemma sigmoid_bound_hi3 : Real.sigmoid (2.94 + 0.48 * 1.96) < 0.9798 := by
  refine sigmoid_lt_of_exp_lt (by norm_num) (lt_of_le_of_lt
    ((show (2.94 : ℝ) + 0.48 * 1.96 = 4 * 0.9702 by norm_num) ▸
      exp_four_mul_le (by norm_num) (by norm_num)) ?_)
  norm_num [expPartialSum, Finset.sum_range_succ, Nat.factorial]

/-- Chapter 7, "Normal Distribution": for `logit(PPV) ~ N(2.94, 0.48²)` the 2.5th, 50th and
97.5th percentiles of the positive predictive value (levels exactly `0.025`, `0.5`, `0.975`)
lie in `(0.8807, 0.8808)`, `(0.9497, 0.9498)` and `(0.9797, 0.9798)`, so they round to the
printed `0.88`, `0.95` and `0.98`. The exact normal quantiles are located by
`Φ(1.96) > 0.975 > Φ(1.9599)` and `Φ(0) = 1/2`. -/
theorem logitNormal_percentiles_example :
    let μ := (gaussianReal 2.94 (Real.toNNReal (0.48 ^ 2))).map Real.sigmoid
    (0.8807 < quantile μ 0.025 ∧ quantile μ 0.025 < 0.8808) ∧
      (0.9497 < quantile μ 0.5 ∧ quantile μ 0.5 < 0.9498) ∧
      (0.9797 < quantile μ 0.975 ∧ quantile μ 0.975 < 0.9798) := by
  intro μ
  have hs : (0 : ℝ) < 0.48 := by norm_num
  have hv : ((Real.toNNReal (0.48 ^ 2) : NNReal) : ℝ) = 0.48 ^ 2 :=
    Real.coe_toNNReal _ (by positivity)
  have hv0 : Real.toNNReal (0.48 ^ 2) ≠ 0 := fun h => by
    rw [Real.toNNReal_eq_zero] at h; norm_num at h
  have hq : ∀ u ∈ Ioo (0 : ℝ) 1, quantile μ u =
      Real.sigmoid (quantile (gaussianReal 2.94 (Real.toNNReal (0.48 ^ 2))) u) := fun u hu =>
    quantile_map Real.sigmoid_strictMono continuous_sigmoid _ hu
  have h196 := cdf_stdNormal_one_ninety_six
  have h19599 := cdf_stdNormal_one_ninety_five_ninety_nine
  have hn196 : cdf (gaussianReal 0 1) (-1.96) < 0.025 := by
    rw [cdf_stdNormal_neg]; linarith [h196.1]
  have hn19599 : 0.025 ≤ cdf (gaussianReal 0 1) (-1.9599) := by
    rw [cdf_stdNormal_neg]; linarith
  have hu1 : (0.025 : ℝ) ∈ Ioo (0 : ℝ) 1 := ⟨by norm_num, by norm_num⟩
  have hu2 : (0.5 : ℝ) ∈ Ioo (0 : ℝ) 1 := ⟨by norm_num, by norm_num⟩
  have hu3 : (0.975 : ℝ) ∈ Ioo (0 : ℝ) 1 := ⟨by norm_num, by norm_num⟩
  have a1 := lt_quantile_gaussianReal (m := 2.94) hs hv hu1 hn196
  have b1 := quantile_gaussianReal_le (m := 2.94) hs hv hu1 hn19599
  have a3 := lt_quantile_gaussianReal (m := 2.94) hs hv hu3 h19599
  have h975 : (0.975 : ℝ) ≤ cdf (gaussianReal 0 1) 1.96 := by linarith [h196.1]
  have b3 := quantile_gaussianReal_le (m := 2.94) hs hv hu3 h975
  have h5 : quantile (gaussianReal 2.94 (Real.toNNReal (0.48 ^ 2))) 0.5 = 2.94 := by
    have h := cdf_gaussianReal_affine 2.94 hs hv 0
    rw [cdf_stdNormal_zero, mul_zero, add_zero] at h
    rw [show (0.5 : ℝ) = 1 / 2 by norm_num, ← h]
    exact quantile_cdf_of_absolutelyContinuous (gaussianReal_absolutelyContinuous' _ hv0) _
  rw [hq _ hu1, hq _ hu2, hq _ hu3, h5]
  refine ⟨⟨?_, ?_⟩, ⟨sigmoid_bound_lo2, sigmoid_bound_hi2⟩, ⟨?_, ?_⟩⟩
  · exact lt_trans sigmoid_bound_lo1 (Real.sigmoid_lt a1)
  · exact lt_of_le_of_lt (Real.sigmoid_le b1) sigmoid_bound_hi1
  · exact lt_trans sigmoid_bound_lo3 (Real.sigmoid_lt a3)
  · exact lt_of_le_of_lt (Real.sigmoid_le b3) sigmoid_bound_hi3

end Percentiles

section GaussianCopula

/-- The correlation matrix `!![1, ρ; ρ, 1]`. -/
def corrMatrix (ρ : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := !![1, ρ; ρ, 1]

/-- For `ρ² ≤ 1` the correlation matrix is positive semidefinite: it is `Aᵀ A` with
`A = !![1, ρ; 0, √(1 - ρ²)]`. -/
lemma corrMatrix_posSemidef {ρ : ℝ} (hρ : ρ ^ 2 ≤ 1) : (corrMatrix ρ).PosSemidef := by
  set A : Matrix (Fin 2) (Fin 2) ℝ := !![1, ρ; 0, Real.sqrt (1 - ρ ^ 2)] with hAdef
  have h := Real.mul_self_sqrt (by linarith : (0 : ℝ) ≤ 1 - ρ ^ 2)
  have hA : corrMatrix ρ = A.conjTranspose * A := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [corrMatrix, hAdef, Matrix.mul_apply, Fin.sum_univ_two]
    nlinarith [h]
  rw [hA]
  exact Matrix.posSemidef_conjTranspose_mul_self A

/-- The standard bivariate normal law with correlation `ρ`: Mathlib's multivariate Gaussian on
`EuclideanSpace ℝ (Fin 2)` with mean `0` and covariance matrix `!![1, ρ; ρ, 1]`. It is the
intended law for `ρ² ≤ 1`, the range in which the matrix is positive semidefinite. -/
noncomputable def bivariateNormal (ρ : ℝ) : Measure (EuclideanSpace ℝ (Fin 2)) :=
  multivariateGaussian 0 (corrMatrix ρ)

/-- The first coordinate of the standard bivariate normal law is standard normal. -/
theorem measurePreserving_bivariateNormal_fst {ρ : ℝ} (hρ : ρ ^ 2 ≤ 1) :
    MeasurePreserving (fun x : EuclideanSpace ℝ (Fin 2) => x 0) (bivariateNormal ρ)
      (gaussianReal 0 1) := by
  simpa [bivariateNormal, corrMatrix] using
    measurePreserving_eval_multivariateGaussian (μ := 0) (corrMatrix_posSemidef hρ) (i := 0)

/-- The second coordinate of the standard bivariate normal law is standard normal. -/
theorem measurePreserving_bivariateNormal_snd {ρ : ℝ} (hρ : ρ ^ 2 ≤ 1) :
    MeasurePreserving (fun x : EuclideanSpace ℝ (Fin 2) => x 1) (bivariateNormal ρ)
      (gaussianReal 0 1) := by
  simpa [bivariateNormal, corrMatrix] using
    measurePreserving_eval_multivariateGaussian (μ := 0) (corrMatrix_posSemidef hρ) (i := 1)

/-- The two coordinates of the standard bivariate normal law have covariance (and, both having
variance one, correlation) `ρ`. -/
theorem covariance_bivariateNormal {ρ : ℝ} (hρ : ρ ^ 2 ≤ 1) :
    cov[fun x : EuclideanSpace ℝ (Fin 2) => x 0, fun x => x 1; bivariateNormal ρ] = ρ := by
  simpa [bivariateNormal, corrMatrix] using
    covariance_eval_multivariateGaussian (μ := 0) (corrMatrix_posSemidef hρ) 0 1

/-- The Gaussian copula `C_ρ(u, v) = P(Φ(Z₁) ≤ u, Φ(Z₂) ≤ v)` for `(Z₁, Z₂)` standard bivariate
normal with correlation `ρ`. -/
noncomputable def gaussianCopula (ρ u v : ℝ) : ℝ :=
  (bivariateNormal ρ).real
    {x | cdf (gaussianReal 0 1) (x 0) ≤ u ∧ cdf (gaussianReal 0 1) (x 1) ≤ v}

lemma measurableSet_copulaRectangle (u v : ℝ) :
    MeasurableSet {x : EuclideanSpace ℝ (Fin 2) |
      cdf (gaussianReal 0 1) (x 0) ≤ u ∧ cdf (gaussianReal 0 1) (x 1) ≤ v} := by
  have hΦ : Measurable (cdf (gaussianReal 0 1)) := (cdf _).mono.measurable
  exact (measurableSet_le (hΦ.comp (by fun_prop)) measurable_const).inter
    (measurableSet_le (hΦ.comp (by fun_prop)) measurable_const)

/-- The NORTA construction with a Gaussian copula (Chapter 7, "Correlated Distributions",
Equation 7.7): if `Z` has the standard bivariate normal law with correlation `ρ` and
`Xᵢ = Q_{μᵢ}(Φ(Zᵢ))`, the joint distribution function of `(X₁, X₂)` is `C_ρ(F₁(x), F₂(y))`,
also when a target law has atoms. -/
theorem measureReal_norta_eq_gaussianCopula {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {ρ : ℝ} (hρ : ρ ^ 2 ≤ 1) {Z : Ω → EuclideanSpace ℝ (Fin 2)}
    (hZ : HasLaw Z (bivariateNormal ρ) P) (μ₁ μ₂ : Measure ℝ) (x y : ℝ) :
    P.real {ω | quantile μ₁ (cdf (gaussianReal 0 1) (Z ω 0)) ≤ x ∧
        quantile μ₂ (cdf (gaussianReal 0 1) (Z ω 1)) ≤ y} =
      gaussianCopula ρ (cdf μ₁ x) (cdf μ₂ y) := by
  have h0 : HasLaw (fun ω => Z ω 0) (gaussianReal 0 1) P :=
    HasLaw.comp (X := Z) (Y := fun x : EuclideanSpace ℝ (Fin 2) => x 0)
      ⟨(measurePreserving_bivariateNormal_fst hρ).measurable.aemeasurable,
        (measurePreserving_bivariateNormal_fst hρ).map_eq⟩ hZ
  have h1 : HasLaw (fun ω => Z ω 1) (gaussianReal 0 1) P :=
    HasLaw.comp (X := Z) (Y := fun x : EuclideanSpace ℝ (Fin 2) => x 1)
      ⟨(measurePreserving_bivariateNormal_snd hρ).measurable.aemeasurable,
        (measurePreserving_bivariateNormal_snd hρ).map_eq⟩ hZ
  rw [measureReal_def, measure_quantile_cdf_gaussian_pair_le h0 h1 μ₁ μ₂ x y, gaussianCopula,
    measureReal_def, ← hZ.map_eq,
    Measure.map_apply_of_aemeasurable hZ.aemeasurable (measurableSet_copulaRectangle _ _)]
  rfl

/-- With `ρ = 0` the Gaussian copula is the independence copula: `C_0(u, v) = u v` on
`[0, 1]²`. -/
theorem gaussianCopula_zero {u v : ℝ} (hu : u ∈ Icc (0 : ℝ) 1) (hv : v ∈ Icc (0 : ℝ) 1) :
    gaussianCopula 0 u v = u * v := by
  have hΦ : Measurable (cdf (gaussianReal 0 1)) := (cdf _).mono.measurable
  have hunif : ∀ w ∈ Icc (0 : ℝ) 1,
      gaussianReal 0 1 (cdf (gaussianReal 0 1) ⁻¹' Iic w) = ENNReal.ofReal w := by
    intro w hw
    rw [← Measure.map_apply hΦ measurableSet_Iic,
      map_cdf_eq_uniform _ continuous_cdf_gaussianReal_zero_one,
      Measure.restrict_apply measurableSet_Iic]
    rcases hw.2.lt_or_eq with h | h
    · have hset : Iic w ∩ Ioo 0 1 = Ioc 0 w := by
        ext t
        simp only [mem_inter_iff, mem_Iic, mem_Ioo, mem_Ioc]
        constructor
        · rintro ⟨h1, h2, _⟩; exact ⟨h2, h1⟩
        · rintro ⟨h1, h2⟩; exact ⟨h2, h1, by linarith⟩
      rw [hset, Real.volume_Ioc, sub_zero]
    · subst h
      rw [inter_eq_right.2 fun t (ht : t ∈ Ioo (0 : ℝ) 1) => (le_of_lt ht.2 : t ≤ 1),
        Real.volume_Ioo, sub_zero]
  have hS : bivariateNormal 0 =
      (Measure.pi fun _ : Fin 2 => gaussianReal 0 1).map (WithLp.toLp 2) := by
    have h1 : corrMatrix 0 = 1 := by
      ext i j; fin_cases i <;> fin_cases j <;> simp [corrMatrix]
    rw [bivariateNormal, h1, multivariateGaussian_zero_one, map_pi_eq_stdGaussian]
  have hpre : WithLp.toLp 2 ⁻¹' {x : EuclideanSpace ℝ (Fin 2) |
        cdf (gaussianReal 0 1) (x 0) ≤ u ∧ cdf (gaussianReal 0 1) (x 1) ≤ v} =
      Set.pi univ fun i : Fin 2 => cdf (gaussianReal 0 1) ⁻¹' Iic (![u, v] i) := by
    ext f
    simp [Fin.forall_fin_two]
  rw [gaussianCopula, measureReal_def, hS,
    Measure.map_apply (by fun_prop) (measurableSet_copulaRectangle _ _), hpre, Measure.pi_pi,
    Fin.prod_univ_two]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [hunif u hu, hunif v hv, ← ENNReal.ofReal_mul hu.1,
    ENNReal.toReal_ofReal (mul_nonneg hu.1 hv.1)]

/-- With `ρ = 0` the NORTA pair has the product joint distribution function `F₁(x) F₂(y)`. -/
theorem measureReal_norta_zero {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {Z : Ω → EuclideanSpace ℝ (Fin 2)} (hZ : HasLaw Z (bivariateNormal 0) P)
    (μ₁ μ₂ : Measure ℝ) [IsProbabilityMeasure μ₁] [IsProbabilityMeasure μ₂] (x y : ℝ) :
    P.real {ω | quantile μ₁ (cdf (gaussianReal 0 1) (Z ω 0)) ≤ x ∧
        quantile μ₂ (cdf (gaussianReal 0 1) (Z ω 1)) ≤ y} = cdf μ₁ x * cdf μ₂ y := by
  rw [measureReal_norta_eq_gaussianCopula (by norm_num) hZ μ₁ μ₂ x y,
    gaussianCopula_zero ⟨cdf_nonneg _ _, cdf_le_one _ _⟩ ⟨cdf_nonneg _ _, cdf_le_one _ _⟩]

end GaussianCopula

section CorrelationExample

open scoped ENNReal

/-- The fair coin: the law on `ℝ` with mass `1/2` at `0` and mass `1/2` at `1`. -/
noncomputable def fairCoin : Measure ℝ := (2⁻¹ : ℝ≥0∞) • (Measure.dirac 0 + Measure.dirac 1)

instance : IsProbabilityMeasure fairCoin :=
  ⟨by rw [fairCoin, smul_apply, add_apply, measure_univ, measure_univ, one_add_one_eq_two,
    smul_eq_mul, ENNReal.inv_mul_cancel two_ne_zero ENNReal.ofNat_ne_top]⟩

/-- The uniform law on `(0, 1)` is a probability measure. -/
instance : IsProbabilityMeasure (volume.restrict (Ioo (0 : ℝ) 1)) :=
  ⟨by rw [Measure.restrict_apply MeasurableSet.univ, univ_inter, Real.volume_Ioo, sub_zero,
    ENNReal.ofReal_one]⟩

lemma cdf_fairCoin (x : ℝ) :
    cdf fairCoin x = (if 0 ≤ x then 2⁻¹ else 0) + (if 1 ≤ x then 2⁻¹ else 0) := by
  rw [cdf_eq_real, measureReal_def, fairCoin]
  simp only [smul_apply, add_apply,
    Measure.dirac_apply' _ measurableSet_Iic, indicator, mem_Iic, Pi.one_apply, smul_eq_mul]
  split_ifs <;> norm_num

/-- The quantile function of the fair coin: for `u ∈ (0, 1)`, `Q(u) = 1` if `u > 1/2` and
`Q(u) = 0` otherwise; the level `u = 1/2` goes to `0`. -/
theorem quantile_fairCoin {u : ℝ} (hu : u ∈ Ioo (0 : ℝ) 1) :
    quantile fairCoin u = if 1 / 2 < u then 1 else 0 := by
  have hq := le_cdf_quantile (μ := fairCoin) hu
  rw [cdf_fairCoin] at hq
  split_ifs with h
  · refine le_antisymm ((quantile_le_iff hu 1).2 ?_) (not_lt.1 fun hlt => ?_)
    · rw [cdf_fairCoin]; norm_num; linarith [hu.2]
    · split_ifs at hq with h1 h2 <;> linarith
  · refine le_antisymm ((quantile_le_iff hu 0).2 ?_) (not_lt.1 fun hlt => ?_)
    · rw [cdf_fairCoin]; norm_num; linarith
    · split_ifs at hq with h1 h2 <;> linarith [hu.1]

lemma cdf_uniform_le (x : ℝ) : cdf (volume.restrict (Ioo (0 : ℝ) 1)) x ≤ max x 0 := by
  rw [cdf_eq_real, measureReal_restrict_apply measurableSet_Iic,
    show max x 0 = volume.real (Ioc 0 x) by rw [Real.volume_real_Ioc, sub_zero]]
  exact measureReal_mono (fun u (hu : u ∈ Iic x ∩ Ioo 0 1) => (⟨hu.2.1, hu.1⟩ : u ∈ Ioc 0 x))
    measure_Ioc_lt_top.ne

lemma le_cdf_uniform {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    x ≤ cdf (volume.restrict (Ioo (0 : ℝ) 1)) x := by
  rw [cdf_eq_real, measureReal_restrict_apply measurableSet_Iic]
  calc x = volume.real (Ioc 0 x) := by rw [Real.volume_real_Ioc_of_le hx.1.le, sub_zero]
    _ ≤ _ := measureReal_mono (fun u (hu : u ∈ Ioc 0 x) =>
        (⟨hu.2, hu.1, lt_of_le_of_lt hu.2 hx.2⟩ : u ∈ Iic x ∩ Ioo 0 1))
      ((measure_mono inter_subset_right).trans_lt measure_Ioo_lt_top).ne

/-- The quantile function of the uniform law on `(0, 1)` is the identity on `(0, 1)`. -/
theorem quantile_uniform {u : ℝ} (hu : u ∈ Ioo (0 : ℝ) 1) :
    quantile (volume.restrict (Ioo (0 : ℝ) 1)) u = u := by
  refine le_antisymm ((quantile_le_iff hu u).2 (le_cdf_uniform hu)) (not_lt.1 fun hlt => ?_)
  have h1 := le_cdf_quantile (μ := volume.restrict (Ioo (0 : ℝ) 1)) hu
  have h2 := cdf_uniform_le (quantile (volume.restrict (Ioo (0 : ℝ) 1)) u)
  rcases le_total (quantile (volume.restrict (Ioo (0 : ℝ) 1)) u) 0 with h | h
  · rw [max_eq_right h] at h2; linarith [hu.1]
  · rw [max_eq_left h] at h2; linarith

lemma setIntegral_Ioo_eq_intervalIntegral {a b : ℝ} (hab : a ≤ b) (f : ℝ → ℝ) :
    ∫ x in Ioo a b, f x = ∫ x in a..b, f x := by
  rw [intervalIntegral.integral_of_le hab, integral_Ioc_eq_integral_Ioo]


/-- Correlation is not preserved by the NORTA construction (Chapter 7, "Correlated
Distributions", Equation 7.7). Take the underlying normal pair `(Z, Z)` with `Z ~ N(0, 1)`: this is
the case `ρ = 1` of `bivariateNormal ρ`, and its correlation is `1`. Transform the first
coordinate to a fair coin and the second to the uniform law on `(0, 1)`. The transformed pair is
`X = Q_coin(Φ(Z)) = 1{Φ(Z) > 1/2}` and `Y = Q_unif(Φ(Z)) = Φ(Z)`; it has the two target
marginals, `Cov(X, Y) = 1/8`, `Var(X) = 1/4`, `Var(Y) = 1/12`, so its Pearson correlation is
`(1/8) / ((1/2)(1/√12)) = √3/2 < 1`. -/
theorem norta_correlation_ne_example {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {Z : Ω → ℝ} (hZ : HasLaw Z (gaussianReal 0 1) P) :
    let X := fun ω => quantile fairCoin (cdf (gaussianReal 0 1) (Z ω))
    let Y := fun ω => quantile (volume.restrict (Ioo (0 : ℝ) 1)) (cdf (gaussianReal 0 1) (Z ω))
    HasLaw X fairCoin P ∧ HasLaw Y (volume.restrict (Ioo (0 : ℝ) 1)) P ∧
      cov[Z, Z; P] / (√Var[Z; P] * √Var[Z; P]) = 1 ∧
      (∀ ω, X ω = if 1 / 2 < cdf (gaussianReal 0 1) (Z ω) then 1 else 0) ∧
      (∀ ω, Y ω = cdf (gaussianReal 0 1) (Z ω)) ∧
      cov[X, Y; P] = 1 / 8 ∧ Var[X; P] = 1 / 4 ∧ Var[Y; P] = 1 / 12 ∧
      cov[X, Y; P] / (√Var[X; P] * √Var[Y; P]) = √3 / 2 ∧ √3 / 2 < 1 := by
  set Φ := cdf (gaussianReal 0 1) with hΦdef
  intro X Y
  have hΦ : ∀ z, Φ z ∈ Ioo (0 : ℝ) 1 :=
    cdf_mem_Ioo_of_absolutelyContinuous (gaussianReal_absolutelyContinuous' 0 one_ne_zero)
  set f : ℝ → ℝ := (Ioi (1 / 2 : ℝ)).indicator 1 with hfdef
  have hfm : Measurable f := measurable_one.indicator measurableSet_Ioi
  have hX : X = fun ω => f (Φ (Z ω)) := funext fun ω => by
    simp only [X, quantile_fairCoin (hΦ _), f, indicator_apply, mem_Ioi, Pi.one_apply]
  have hY : Y = fun ω => id (Φ (Z ω)) := funext fun ω => quantile_uniform (hΦ _)
  have hU : HasLaw (fun ω => Φ (Z ω)) (volume.restrict (Ioo (0 : ℝ) 1)) P :=
    hasLaw_cdf_uniform hZ continuous_cdf_gaussianReal_zero_one
  have hfL : MemLp f 2 (volume.restrict (Ioo (0 : ℝ) 1)) :=
    (memLp_const 1).indicator measurableSet_Ioi.nullMeasurableSet
  have hidL : MemLp id 2 (volume.restrict (Ioo (0 : ℝ) 1)) :=
    MemLp.of_bound aestronglyMeasurable_id 1 ((ae_restrict_iff' measurableSet_Ioo).2
      (ae_of_all _ fun u hu => by
        rw [id, Real.norm_eq_abs, abs_le]; constructor <;> linarith [hu.1, hu.2]))
  have hset : Ioi (1 / 2 : ℝ) ∩ Ioo 0 1 = Ioo (1 / 2) 1 := by
    ext u
    simp only [mem_inter_iff, mem_Ioi, mem_Ioo]
    constructor
    · rintro ⟨h1, -, h3⟩; exact ⟨h1, h3⟩
    · rintro ⟨h1, h2⟩; exact ⟨h1, by linarith, h2⟩
  have I_f : ∫ u, f u ∂(volume.restrict (Ioo (0 : ℝ) 1)) = 1 / 2 := by
    rw [integral_indicator_one measurableSet_Ioi, measureReal_restrict_apply measurableSet_Ioi,
      hset, Real.volume_real_Ioo_of_le (by norm_num)]
    norm_num
  have I_ff : ∫ u, (f ^ 2) u ∂(volume.restrict (Ioo (0 : ℝ) 1)) = 1 / 2 := by
    have : f ^ 2 = f := funext fun u => by
      simp only [Pi.pow_apply, f, indicator_apply, Pi.one_apply]
      split_ifs <;> norm_num
    rw [this, I_f]
  have I_id : ∫ u, id u ∂(volume.restrict (Ioo (0 : ℝ) 1)) = 1 / 2 := by
    simp only [id]
    rw [setIntegral_Ioo_eq_intervalIntegral zero_le_one, integral_id]
    norm_num
  have I_idd : ∫ u, (id ^ 2) u ∂(volume.restrict (Ioo (0 : ℝ) 1)) = 1 / 3 := by
    simp only [Pi.pow_apply, id]
    rw [setIntegral_Ioo_eq_intervalIntegral zero_le_one, integral_pow]
    norm_num
  have I_fid : ∫ u, (f * (id : ℝ → ℝ)) u ∂(volume.restrict (Ioo (0 : ℝ) 1)) = 3 / 8 := by
    have : f * (id : ℝ → ℝ) = (Ioi (1 / 2 : ℝ)).indicator id := funext fun u => by
      simp only [Pi.mul_apply, f, indicator_apply, Pi.one_apply, id]
      split_ifs <;> simp
    rw [this, integral_indicator measurableSet_Ioi, Measure.restrict_restrict measurableSet_Ioi,
      hset]
    simp only [id]
    rw [setIntegral_Ioo_eq_intervalIntegral (by norm_num), integral_id]
    norm_num
  have hcov : cov[X, Y; P] = 1 / 8 := by
    rw [hX, hY, hU.covariance_fun_comp hfm.aemeasurable aemeasurable_id,
      covariance_eq_sub hfL hidL, I_fid, I_f, I_id]
    norm_num
  have hvX : Var[X; P] = 1 / 4 := by
    rw [hX, show (fun ω => f (Φ (Z ω))) = f ∘ (fun ω => Φ (Z ω)) from rfl,
      ← variance_map (by rw [hU.map_eq]; exact hfm.aemeasurable) hU.aemeasurable, hU.map_eq,
      variance_eq_sub hfL, I_ff, I_f]
    norm_num
  have hvY : Var[Y; P] = 1 / 12 := by
    rw [hY, show (fun ω => id (Φ (Z ω))) = id ∘ (fun ω => Φ (Z ω)) from rfl,
      ← variance_map (by rw [hU.map_eq]; exact aemeasurable_id) hU.aemeasurable, hU.map_eq,
      variance_eq_sub hidL, I_idd, I_id]
    norm_num
  have hvZ : Var[Z; P] = 1 := by
    rw [hZ.variance_eq, variance_id_gaussianReal]
    simp
  have h3 : (0 : ℝ) < √3 := by positivity
  have h4 : √(1 / 4 : ℝ) = 1 / 2 := by
    rw [show (1 / 4 : ℝ) = (1 / 2) ^ 2 by norm_num]
    exact Real.sqrt_sq (by norm_num)
  have h12 : √(1 / 12 : ℝ) = √3 / 6 := by
    rw [show (1 / 12 : ℝ) = (√3 / 6) ^ 2 by rw [div_pow, Real.sq_sqrt (by norm_num)]; norm_num]
    exact Real.sqrt_sq (by positivity)
  have hlt : √3 < 2 := by
    rw [show (2 : ℝ) = √4 by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  refine ⟨?_, ?_, ?_, fun ω => ?_, fun ω => quantile_uniform (hΦ _), hcov, hvX, hvY, ?_, ?_⟩
  · exact hasLaw_quantile_cdf_gaussian hZ fairCoin
  · exact hasLaw_quantile_cdf_gaussian hZ _
  · rw [covariance_self hZ.aemeasurable, hvZ]
    simp
  · simp only [X, quantile_fairCoin (hΦ _)]
  · rw [hcov, hvX, hvY, h4, h12]
    field_simp
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)]
  · linarith

end CorrelationExample

section BivariateNormalLinks

open Complex

/-- The bivariate normal law is a probability measure. -/
instance (ρ : ℝ) : IsProbabilityMeasure (bivariateNormal ρ) := by
  unfold bivariateNormal; infer_instance

/-- The characteristic function of `bivariateNormal ρ`:
`t ↦ exp(-(t₁² + 2ρ t₁ t₂ + t₂²)/2)`. -/
lemma charFun_bivariateNormal {ρ : ℝ} (hρ : ρ ^ 2 ≤ 1) (t : EuclideanSpace ℝ (Fin 2)) :
    charFun (bivariateNormal ρ) t =
      cexp (-((t 0 ^ 2 + 2 * ρ * t 0 * t 1 + t 1 ^ 2 : ℝ) : ℂ) / 2) := by
  rw [bivariateNormal, charFun_multivariateGaussian (corrMatrix_posSemidef hρ)]
  congr 1
  simp [corrMatrix, dotProduct, Matrix.mulVec, Fin.sum_univ_two]
  ring

/-- The diagonal pair `(Z, Z)` of a standard normal `Z` has law `bivariateNormal 1`. -/
theorem map_diag_gaussianReal :
    (gaussianReal 0 1).map (fun z : ℝ => !₂[z, z]) = bivariateNormal 1 := by
  have hm : Measurable (fun z : ℝ => !₂[z, z]) := by fun_prop
  apply Measure.ext_of_charFun
  funext t
  rw [charFun_bivariateNormal (by norm_num), charFun_apply, integral_map hm.aemeasurable
    (by fun_prop)]
  have h : ∀ z : ℝ, ((inner ℝ !₂[z, z] t : ℝ) : ℂ) = ((t 0 + t 1 : ℝ) : ℂ) * z := fun z => by
    simp [PiLp.inner_apply, Fin.sum_univ_two]
    ring
  simp_rw [h]
  rw [← charFun_apply_real, charFun_gaussianReal]
  congr 1
  push_cast
  ring

/-- The cyclic map `(z₁, z₂) ↦ (z₂ - z₁, -z₁)` preserves `bivariateNormal (1/2)`. -/
theorem map_cyclic_bivariateNormal_half :
    (bivariateNormal (1 / 2)).map (fun x : EuclideanSpace ℝ (Fin 2) => !₂[x 1 - x 0, -x 0]) =
      bivariateNormal (1 / 2) := by
  have hm : Measurable (fun x : EuclideanSpace ℝ (Fin 2) => !₂[x 1 - x 0, -x 0]) := by fun_prop
  apply Measure.ext_of_charFun
  funext t
  rw [charFun_bivariateNormal (by norm_num), charFun_apply, integral_map hm.aemeasurable
    (by fun_prop)]
  have h : ∀ x : EuclideanSpace ℝ (Fin 2),
      ((inner ℝ !₂[x 1 - x 0, -x 0] t : ℝ) : ℂ) = ((inner ℝ x !₂[-t 0 - t 1, t 0] : ℝ) : ℂ) :=
      fun x => by
    simp [PiLp.inner_apply, Fin.sum_univ_two]
    ring
  simp_rw [h]
  rw [← charFun_apply, charFun_bivariateNormal (by norm_num)]
  congr 1
  simp
  ring

/-- A coordinate of a bivariate normal pair has a null level set. -/
lemma bivariateNormal_coord_eq_zero {ρ : ℝ} (hρ : ρ ^ 2 ≤ 1) (i : Fin 2) :
    bivariateNormal ρ {x | x i = 0} = 0 := by
  have : NullSingletonClass (gaussianReal 0 1) := nullSingletonClass_gaussianReal one_ne_zero
  have hmp : MeasurePreserving (fun x : EuclideanSpace ℝ (Fin 2) => x i) (bivariateNormal ρ)
      (gaussianReal 0 1) := by
    fin_cases i
    · exact measurePreserving_bivariateNormal_fst hρ
    · exact measurePreserving_bivariateNormal_snd hρ
  rw [show {x : EuclideanSpace ℝ (Fin 2) | x i = 0} = (fun x => x i) ⁻¹' {0} from rfl,
    hmp.measure_preimage (measurableSet_singleton 0).nullMeasurableSet]
  exact measure_singleton 0

/-- The orthant probability at `ρ = 1/2`: `P(Z₁ > 0, Z₂ > 0) = 1/3` for `(Z₁, Z₂)` with law
`bivariateNormal (1/2)` (the general value is `1/4 + arcsin ρ / (2π)`). With
`A = Z₁`, `B = Z₂ - Z₁`, `C = -Z₂`, the triple `(A, B, C)` has the same law as its cyclic shift
`(B, C, A)` (`map_cyclic_bivariateNormal_half`), and `A + B + C = 0`. Off the null set where one
of them vanishes, exactly one of the events `{A > 0, C < 0}`, `{B > 0, A < 0}`, `{C > 0, B < 0}`
occurs; the three are congruent, so each has probability `1/3`, and the first is the orthant. -/
theorem bivariateNormal_half_orthant :
    (bivariateNormal (1 / 2)).real {x | 0 < x 0 ∧ 0 < x 1} = 1 / 3 := by
  set μ := bivariateNormal (1 / 2) with hμ
  set T : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2) := fun x => !₂[x 1 - x 0, -x 0]
  have hTm : Measurable T := by fun_prop
  have hT : MeasurePreserving T μ μ := ⟨hTm, map_cyclic_bivariateNormal_half⟩
  have hmeas : ∀ (f g : EuclideanSpace ℝ (Fin 2) → ℝ), Measurable f → Measurable g →
      MeasurableSet {x | 0 < f x ∧ 0 < g x} := fun f g hf hg => by
    change MeasurableSet ({x | (0 : ℝ) < f x} ∩ {x | (0 : ℝ) < g x})
    exact (measurableSet_lt measurable_const hf).inter (measurableSet_lt measurable_const hg)
  set F₁ := {x : EuclideanSpace ℝ (Fin 2) | 0 < x 0 ∧ 0 < x 1}
  set F₂ := {x : EuclideanSpace ℝ (Fin 2) | 0 < x 1 - x 0 ∧ 0 < -x 0}
  set F₃ := {x : EuclideanSpace ℝ (Fin 2) | 0 < -x 1 ∧ 0 < x 0 - x 1}
  have hF₁ : MeasurableSet F₁ := hmeas _ _ (by fun_prop) (by fun_prop)
  have hF₂ : MeasurableSet F₂ := hmeas _ _ (by fun_prop) (by fun_prop)
  have hF₃ : MeasurableSet F₃ := hmeas _ _ (by fun_prop) (by fun_prop)
  have h₂ : T ⁻¹' F₁ = F₂ := by ext x; simp [T, F₁, F₂]
  have h₃ : T ⁻¹' F₂ = F₃ := by
    ext x
    change (0 < (T x) 1 - (T x) 0 ∧ 0 < -(T x) 0) ↔ (0 < -x 1 ∧ 0 < x 0 - x 1)
    have e0 : (T x) 0 = x 1 - x 0 := by simp [T]
    have e1 : (T x) 1 = -x 0 := by simp [T]
    rw [e0, e1]
    constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith
  have e₂ : μ.real F₂ = μ.real F₁ := by
    rw [measureReal_def, measureReal_def, ← h₂, hT.measure_preimage hF₁.nullMeasurableSet]
  have e₃ : μ.real F₃ = μ.real F₂ := by
    rw [measureReal_def, measureReal_def, ← h₃, hT.measure_preimage hF₂.nullMeasurableSet]
  -- the null set where `A`, `C` or `B` vanishes
  set N := {x : EuclideanSpace ℝ (Fin 2) | x 0 = 0} ∪ {x | x 1 = 0} ∪ T ⁻¹' {x | x 0 = 0}
  have hN : μ N = 0 := by
    refine measure_union_null (measure_union_null (bivariateNormal_coord_eq_zero (by norm_num) 0)
      (bivariateNormal_coord_eq_zero (by norm_num) 1)) ?_
    rw [hT.measure_preimage (measurableSet_eq_fun (by fun_prop) measurable_const).nullMeasurableSet]
    exact bivariateNormal_coord_eq_zero (by norm_num) 0
  have hcover : Nᶜ ⊆ F₁ ∪ F₂ ∪ F₃ := by
    intro x hx
    simp only [N, T, mem_compl_iff, mem_union, mem_ofPred_eq, mem_preimage, not_or] at hx
    simp only [Matrix.cons_val_zero] at hx
    obtain ⟨⟨h0, h1⟩, h2⟩ := hx
    have h2' : x 1 ≠ x 0 := fun h => h2 (by rw [h, sub_self])
    simp only [F₁, F₂, F₃, mem_union, mem_ofPred_eq]
    rcases lt_or_gt_of_ne h0 with a | a <;> rcases lt_or_gt_of_ne h1 with b | b <;>
      rcases lt_or_gt_of_ne h2' with c | c
    all_goals first
      | exact Or.inl (Or.inl ⟨by linarith, by linarith⟩)
      | exact Or.inl (Or.inr ⟨by linarith, by linarith⟩)
      | exact Or.inr ⟨by linarith, by linarith⟩
  have hd₁₂ : Disjoint F₁ F₂ := disjoint_left.2 fun x h h' => by
    simp only [F₁, F₂, mem_ofPred_eq] at h h'; linarith [h.1, h'.2]
  have hd₃ : Disjoint (F₁ ∪ F₂) F₃ := disjoint_left.2 fun x h h' => by
    simp only [F₁, F₂, F₃, mem_union, mem_ofPred_eq] at h h'
    rcases h with h | h <;> linarith [h.1, h.2, h'.1, h'.2]
  have hU : μ.real (F₁ ∪ F₂ ∪ F₃) = 1 := by
    refine le_antisymm measureReal_le_one ?_
    have hNc : μ.real Nᶜ = 1 := by
      rw [probReal_compl_eq_one_sub₀ (NullMeasurableSet.of_null hN), measureReal_def, hN,
        ENNReal.toReal_zero, sub_zero]
    exact hNc ▸ measureReal_mono hcover
  rw [measureReal_union hd₃ hF₃, measureReal_union hd₁₂ hF₂, e₃, e₂] at hU
  linarith

/-- For `z ∈ ℝ`, `Φ(z) > 1/2` exactly when `z > 0`. -/
lemma half_lt_cdf_stdNormal_iff (z : ℝ) : 1 / 2 < cdf (gaussianReal 0 1) z ↔ 0 < z := by
  rw [← cdf_stdNormal_zero]
  constructor
  · intro h
    by_contra hz
    exact absurd ((cdf (gaussianReal 0 1)).mono (not_lt.1 hz)) (not_le.2 h)
  · intro hz
    by_contra h
    have h2 := (cdf (gaussianReal 0 1)).measure_Ioc 0 z
    rw [measure_cdf, ENNReal.ofReal_eq_zero.2 (by linarith [not_lt.1 h])] at h2
    have := gaussianReal_absolutelyContinuous' 0 one_ne_zero h2
    rw [Real.volume_Ioc, ENNReal.ofReal_eq_zero] at this
    linarith

/-- The fair coin quantile of `Φ(z)` is the indicator of `z > 0`. -/
lemma quantile_fairCoin_cdf_stdNormal (z : ℝ) :
    quantile fairCoin (cdf (gaussianReal 0 1) z) = (Ioi (0 : ℝ)).indicator 1 z := by
  rw [quantile_fairCoin (cdf_mem_Ioo_of_absolutelyContinuous
    (gaussianReal_absolutelyContinuous' 0 one_ne_zero) z)]
  simp only [half_lt_cdf_stdNormal_iff, indicator_apply, mem_Ioi, Pi.one_apply]

/-- The variance of `f(W)` depends only on the law `ν` of `W`. -/
lemma variance_fun_comp_of_hasLaw {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {Q : Measure Ω} {ν : Measure Ω'} {W : Ω → Ω'} (hW : HasLaw W ν Q) {f : Ω' → ℝ}
    (hf : Measurable f) : Var[fun ω => f (W ω); Q] = Var[f; ν] := by
  rw [← hW.map_eq, variance_map hf.aemeasurable hW.aemeasurable]
  rfl

/-- The `ρ = 1` example of `norta_correlation_ne_example`, stated for a pair `Z` with law
`bivariateNormal 1`: transforming its first coordinate to a fair coin and its second to the
uniform law gives correlation `√3/2`, while the correlation of `Z` is `1`. The pair `(Z, Z)` of
that theorem has law `bivariateNormal 1` by `map_diag_gaussianReal`. -/
theorem norta_correlation_ne_bivariateNormal_one {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {Z : Ω → EuclideanSpace ℝ (Fin 2)}
    (hZ : HasLaw Z (bivariateNormal 1) P) :
    let X := fun ω => quantile fairCoin (cdf (gaussianReal 0 1) (Z ω 0))
    let Y := fun ω => quantile (volume.restrict (Ioo (0 : ℝ) 1)) (cdf (gaussianReal 0 1) (Z ω 1))
    HasLaw X fairCoin P ∧ HasLaw Y (volume.restrict (Ioo (0 : ℝ) 1)) P ∧
      cov[fun ω => Z ω 0, fun ω => Z ω 1; P] = 1 ∧
      cov[X, Y; P] = 1 / 8 ∧ Var[X; P] = 1 / 4 ∧ Var[Y; P] = 1 / 12 ∧
      cov[X, Y; P] / (√Var[X; P] * √Var[Y; P]) = √3 / 2 := by
  intro X Y
  have hρ : (1 : ℝ) ^ 2 ≤ 1 := by norm_num
  have hZ0 : HasLaw (fun ω => Z ω 0) (gaussianReal 0 1) P :=
    HasLaw.comp (X := Z) (Y := fun x : EuclideanSpace ℝ (Fin 2) => x 0)
      ⟨(measurePreserving_bivariateNormal_fst hρ).measurable.aemeasurable,
        (measurePreserving_bivariateNormal_fst hρ).map_eq⟩ hZ
  have hZ1 : HasLaw (fun ω => Z ω 1) (gaussianReal 0 1) P :=
    HasLaw.comp (X := Z) (Y := fun x : EuclideanSpace ℝ (Fin 2) => x 1)
      ⟨(measurePreserving_bivariateNormal_snd hρ).measurable.aemeasurable,
        (measurePreserving_bivariateNormal_snd hρ).map_eq⟩ hZ
  have hd : HasLaw (fun z : ℝ => !₂[z, z]) (bivariateNormal 1) (gaussianReal 0 1) :=
    ⟨(by fun_prop : Measurable fun z : ℝ => !₂[z, z]).aemeasurable, map_diag_gaussianReal⟩
  set F : EuclideanSpace ℝ (Fin 2) → ℝ :=
    fun x => quantile fairCoin (cdf (gaussianReal 0 1) (x 0))
  set G : EuclideanSpace ℝ (Fin 2) → ℝ :=
    fun x => quantile (volume.restrict (Ioo (0 : ℝ) 1)) (cdf (gaussianReal 0 1) (x 1))
  have hF : Measurable F := (measurable_quantile _).comp
    ((cdf (gaussianReal 0 1)).mono.measurable.comp (by fun_prop))
  have hG : Measurable G := (measurable_quantile _).comp
    ((cdf (gaussianReal 0 1)).mono.measurable.comp (by fun_prop))
  obtain ⟨-, -, -, -, -, hc, hv1, hv2, hr, -⟩ :=
    norta_correlation_ne_example (P := gaussianReal 0 1) (Z := id) HasLaw.id
  have hcov : cov[X, Y; P] = 1 / 8 := by
    rw [show X = fun ω => F (Z ω) from rfl, show Y = fun ω => G (Z ω) from rfl,
      hZ.covariance_fun_comp hF.aemeasurable hG.aemeasurable,
      ← hd.covariance_fun_comp hF.aemeasurable hG.aemeasurable]
    simpa [F, G] using hc
  have hvX : Var[X; P] = 1 / 4 := by
    rw [show X = fun ω => F (Z ω) from rfl, variance_fun_comp_of_hasLaw hZ hF,
      ← variance_fun_comp_of_hasLaw hd hF]
    simpa [F] using hv1
  have hvY : Var[Y; P] = 1 / 12 := by
    rw [show Y = fun ω => G (Z ω) from rfl, variance_fun_comp_of_hasLaw hZ hG,
      ← variance_fun_comp_of_hasLaw hd hG]
    simpa [G] using hv2
  refine ⟨hasLaw_quantile_cdf_gaussian hZ0 _, hasLaw_quantile_cdf_gaussian hZ1 _, ?_, hcov, hvX,
    hvY, ?_⟩
  · rw [hZ.covariance_fun_comp (f := fun x : EuclideanSpace ℝ (Fin 2) => x 0)
      (g := fun x : EuclideanSpace ℝ (Fin 2) => x 1) (Measurable.aemeasurable (by fun_prop))
      (Measurable.aemeasurable (by fun_prop))]
    exact covariance_bivariateNormal hρ
  · rw [hcov, hvX, hvY, ← hc, ← hv1, ← hv2]
    exact hr

/-- An interior value of `ρ` at which the NORTA construction changes the correlation: for a pair
`Z` with law `bivariateNormal (1/2)` (correlation `1/2`) and fair coin targets for both
coordinates, the transformed pair is `X = 1{Z₁ > 0}`, `Y = 1{Z₂ > 0}`, with
`P(X = 1, Y = 1) = 1/3` (`bivariateNormal_half_orthant`), `Cov(X, Y) = 1/3 - 1/4 = 1/12` and
`Var(X) = Var(Y) = 1/4`, so its correlation is `1/3 ≠ 1/2`. -/
theorem norta_correlation_ne_bivariateNormal_half {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {Z : Ω → EuclideanSpace ℝ (Fin 2)}
    (hZ : HasLaw Z (bivariateNormal (1 / 2)) P) :
    let X := fun ω => quantile fairCoin (cdf (gaussianReal 0 1) (Z ω 0))
    let Y := fun ω => quantile fairCoin (cdf (gaussianReal 0 1) (Z ω 1))
    HasLaw X fairCoin P ∧ HasLaw Y fairCoin P ∧
      cov[fun ω => Z ω 0, fun ω => Z ω 1; P] = 1 / 2 ∧
      P.real {ω | X ω = 1 ∧ Y ω = 1} = 1 / 3 ∧
      cov[X, Y; P] = 1 / 12 ∧ Var[X; P] = 1 / 4 ∧ Var[Y; P] = 1 / 4 ∧
      cov[X, Y; P] / (√Var[X; P] * √Var[Y; P]) = 1 / 3 := by
  intro X Y
  have hρ : (1 / 2 : ℝ) ^ 2 ≤ 1 := by norm_num
  set μ := bivariateNormal (1 / 2)
  have hZ0 : HasLaw (fun ω => Z ω 0) (gaussianReal 0 1) P :=
    HasLaw.comp (X := Z) (Y := fun x : EuclideanSpace ℝ (Fin 2) => x 0)
      ⟨(measurePreserving_bivariateNormal_fst hρ).measurable.aemeasurable,
        (measurePreserving_bivariateNormal_fst hρ).map_eq⟩ hZ
  have hZ1 : HasLaw (fun ω => Z ω 1) (gaussianReal 0 1) P :=
    HasLaw.comp (X := Z) (Y := fun x : EuclideanSpace ℝ (Fin 2) => x 1)
      ⟨(measurePreserving_bivariateNormal_snd hρ).measurable.aemeasurable,
        (measurePreserving_bivariateNormal_snd hρ).map_eq⟩ hZ
  set A := {x : EuclideanSpace ℝ (Fin 2) | 0 < x 0}
  set B := {x : EuclideanSpace ℝ (Fin 2) | 0 < x 1}
  have hA : MeasurableSet A := measurableSet_lt measurable_const (by fun_prop)
  have hB : MeasurableSet B := measurableSet_lt measurable_const (by fun_prop)
  have hX : X = fun ω => A.indicator 1 (Z ω) := funext fun ω => by
    simp only [X, quantile_fairCoin_cdf_stdNormal, indicator_apply, A, mem_Ioi, mem_ofPred_eq,
      Pi.one_apply]
  have hY : Y = fun ω => B.indicator 1 (Z ω) := funext fun ω => by
    simp only [Y, quantile_fairCoin_cdf_stdNormal, indicator_apply, B, mem_Ioi, mem_ofPred_eq,
      Pi.one_apply]
  have hAm : Measurable (A.indicator (1 : EuclideanSpace ℝ (Fin 2) → ℝ)) :=
    measurable_one.indicator hA
  have hBm : Measurable (B.indicator (1 : EuclideanSpace ℝ (Fin 2) → ℝ)) :=
    measurable_one.indicator hB
  have hAL : MemLp (A.indicator (1 : EuclideanSpace ℝ (Fin 2) → ℝ)) 2 μ :=
    (memLp_const 1).indicator hA.nullMeasurableSet
  have hBL : MemLp (B.indicator (1 : EuclideanSpace ℝ (Fin 2) → ℝ)) 2 μ :=
    (memLp_const 1).indicator hB.nullMeasurableSet
  have hhalf : (gaussianReal 0 1).real (Ioi 0) = 1 / 2 := by
    rw [← compl_Iic, probReal_compl_eq_one_sub measurableSet_Iic, ← cdf_eq_real,
      cdf_stdNormal_zero]
    norm_num
  have IA : ∫ x, A.indicator (1 : EuclideanSpace ℝ (Fin 2) → ℝ) x ∂μ = 1 / 2 := by
    rw [integral_indicator_one hA, measureReal_def, show A = (fun x => x 0) ⁻¹' Ioi 0 from rfl,
      (measurePreserving_bivariateNormal_fst hρ).measure_preimage
        measurableSet_Ioi.nullMeasurableSet, ← measureReal_def, hhalf]
  have IB : ∫ x, B.indicator (1 : EuclideanSpace ℝ (Fin 2) → ℝ) x ∂μ = 1 / 2 := by
    rw [integral_indicator_one hB, measureReal_def, show B = (fun x => x 1) ⁻¹' Ioi 0 from rfl,
      (measurePreserving_bivariateNormal_snd hρ).measure_preimage
        measurableSet_Ioi.nullMeasurableSet, ← measureReal_def, hhalf]
  have IAB : ∫ x, (A.indicator 1 * B.indicator 1 : EuclideanSpace ℝ (Fin 2) → ℝ) x ∂μ =
      1 / 3 := by
    rw [← inter_indicator_one, integral_indicator_one (hA.inter hB)]
    exact bivariateNormal_half_orthant
  have hsq : ∀ s : Set (EuclideanSpace ℝ (Fin 2)),
      (s.indicator (1 : EuclideanSpace ℝ (Fin 2) → ℝ)) ^ 2 = s.indicator 1 := fun s =>
    funext fun x => by by_cases hx : x ∈ s <;> simp [hx]
  have hcov : cov[X, Y; P] = 1 / 12 := by
    rw [hX, hY, hZ.covariance_fun_comp hAm.aemeasurable hBm.aemeasurable,
      covariance_eq_sub hAL hBL, IAB, IA, IB]
    norm_num
  have hvX : Var[X; P] = 1 / 4 := by
    rw [hX, variance_fun_comp_of_hasLaw hZ hAm, variance_eq_sub hAL, hsq, IA]
    norm_num
  have hvY : Var[Y; P] = 1 / 4 := by
    rw [hY, variance_fun_comp_of_hasLaw hZ hBm, variance_eq_sub hBL, hsq, IB]
    norm_num
  have hev : {ω | X ω = 1 ∧ Y ω = 1} = Z ⁻¹' {x | 0 < x 0 ∧ 0 < x 1} := by
    ext ω
    simp only [hX, hY, indicator_apply, A, B, mem_ofPred_eq, mem_preimage, Pi.one_apply]
    split_ifs <;> simp_all
  have h4 : √(1 / 4 : ℝ) = 1 / 2 := by
    rw [show (1 / 4 : ℝ) = (1 / 2) ^ 2 by norm_num]
    exact Real.sqrt_sq (by norm_num)
  refine ⟨hasLaw_quantile_cdf_gaussian hZ0 _, hasLaw_quantile_cdf_gaussian hZ1 _, ?_, ?_, hcov,
    hvX, hvY, ?_⟩
  · rw [hZ.covariance_fun_comp (f := fun x : EuclideanSpace ℝ (Fin 2) => x 0)
      (g := fun x : EuclideanSpace ℝ (Fin 2) => x 1) (Measurable.aemeasurable (by fun_prop))
      (Measurable.aemeasurable (by fun_prop))]
    exact covariance_bivariateNormal hρ
  · rw [hev, measureReal_def, ← Measure.map_apply_of_aemeasurable hZ.aemeasurable
      (show MeasurableSet {x : EuclideanSpace ℝ (Fin 2) | 0 < x 0 ∧ 0 < x 1} from hA.inter hB),
      hZ.map_eq, ← measureReal_def]
    exact bivariateNormal_half_orthant
  · rw [hcov, hvX, hvY, h4]
    norm_num

end BivariateNormalLinks

end Distributions

end BiasAnalysis

end CausalInference
