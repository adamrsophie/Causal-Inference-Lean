/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import Mathlib.Analysis.Complex.AbelLimit
public import Mathlib.Analysis.Calculus.SmoothSeries
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.SpecificLimits.Normed
public import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
public import Mathlib.Probability.Independence.Integration
public import Mathlib.Probability.Moments.Basic

/-!
# Probability generating functions

For a law `ν` on `ℕ` the **probability generating function** is `G_ν(z) = ∫ z ^ k ν(dk)`
(`generatingFunction`); for a count `X` with law `μ.map X` it is `E[z ^ X]`
(`generatingFunction_map`). This file proves the facts about `G` used for aggregate count
likelihoods.

* **Power series form** (`hasSum_generatingFunction`): for `|z| ≤ 1`,
  `G_ν(z) = ∑ ν{k} z ^ k`, and `G_ν(1) = 1`.
* **Expectations as series** (`integrable_iff_summable_mass`, `hasSum_integral_mass`): `g` is
  `ν` integrable exactly when `∑ ν{k} |g k|` converges, and then `∫ g dν = ∑ ν{k} g k`.
* **Smoothness inside the unit disk** (`iteratedDeriv_generatingFunction_eqOn`,
  `hasDerivAt_iteratedDeriv_generatingFunction`): on `(-1, 1)` the `r`-th derivative is the
  series `∑ k (k - 1) ⋯ (k - r + 1) ν{k} z ^ (k - r)`, differentiated term by term.
* **The mass function from the derivatives at the origin**
  (`measureReal_singleton_eq_iteratedDeriv`): `ν{k} = G_ν^(k)(0) / k!`.
* **Factorial moments from the derivatives at one** (`tendsto_iteratedDeriv_generatingFunction`,
  `integrable_descFactorial_of_tendsto`): the `r`-th derivative has a finite limit as `z ↑ 1`
  exactly when the factorial moment `∫ k (k - 1) ⋯ (k - r + 1) dν` is finite, and the limit is
  that moment. The proof is Abel's theorem and its converse for nonnegative coefficients.
* **Uniqueness** (`eq_of_generatingFunction_eqOn`): a law on `ℕ` is determined by its
  generating function on `(-1, 1)`.
* **The product rule** (`generatingFunction_map_sum`, `generatingFunction_map_add`): the
  generating function of a sum of independent counts is the product of their generating
  functions, for `|z| ≤ 1`, where every `z ^ X` is integrable.
* **The moment generating function** (`generatingFunction_map_eq_mgf`): `G(z) = M(log z)` for
  `z > 0`.

## Main definitions

* `generatingFunction`, `factorialSeries`.

## Main results

* `hasSum_generatingFunction`, `generatingFunction_one`, `generatingFunction_map`.
* `measureReal_singleton_eq_iteratedDeriv`, `tendsto_iteratedDeriv_generatingFunction`,
  `integrable_descFactorial_of_tendsto`, `hasDerivAt_iteratedDeriv_generatingFunction`.
* `eq_of_generatingFunction_eqOn`, `generatingFunction_map_sum`, `generatingFunction_map_add`,
  `generatingFunction_map_eq_mgf`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology Set Finset

namespace CausalInference

namespace NetworkMetaRegression

/-! ### The factorial series -/

section Series

variable {q : ℕ → ℝ}

/-- The **factorial series** `∑ k (k - 1) ⋯ (k - r + 1) q k z ^ (k - r)`: the `r`-th derivative
of the power series with coefficients `q`. -/
noncomputable def factorialSeries (q : ℕ → ℝ) (r : ℕ) (z : ℝ) : ℝ :=
  ∑' k, (k.descFactorial r : ℝ) * q k * z ^ (k - r)

private lemma factorialSeries_term_le (hq0 : ∀ k, 0 ≤ q k) (hq1 : ∀ k, q k ≤ 1) {ρ : ℝ}
    (hρ : 0 < ρ) {y : ℝ} (hy : |y| ≤ ρ) (r k : ℕ) :
    ‖(k.descFactorial r : ℝ) * q k * y ^ (k - r)‖ ≤ (k : ℝ) ^ r * ρ ^ k / ρ ^ r := by
  by_cases h : r ≤ k
  · calc ‖(k.descFactorial r : ℝ) * q k * y ^ (k - r)‖
          = (k.descFactorial r : ℝ) * q k * |y| ^ (k - r) := by
            rw [norm_mul, norm_mul, norm_pow, Real.norm_natCast, Real.norm_of_nonneg (hq0 k),
              Real.norm_eq_abs]
      _ ≤ (k : ℝ) ^ r * 1 * ρ ^ (k - r) :=
            mul_le_mul (mul_le_mul (by exact_mod_cast Nat.descFactorial_le_pow k r) (hq1 k)
              (hq0 k) (by positivity)) (pow_le_pow_left₀ (abs_nonneg y) hy _) (by positivity)
              (by positivity)
      _ = (k : ℝ) ^ r * ρ ^ k / ρ ^ r := by
            rw [mul_one, mul_div_assoc, pow_sub₀ ρ hρ.ne' h, div_eq_mul_inv]
  · rw [Nat.descFactorial_eq_zero_iff_lt.mpr (by omega)]
    simp only [Nat.cast_zero, zero_mul, norm_zero]
    positivity

private lemma summable_factorialSeries_bound {ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (r : ℕ) :
    Summable fun k : ℕ => (k : ℝ) ^ r * ρ ^ k / ρ ^ r := by
  have hn : ‖ρ‖ < 1 := by rwa [Real.norm_of_nonneg hρ0.le]
  exact (summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) r hn).div_const (ρ ^ r)

/-- Inside the unit disk the factorial series of coefficients in `[0, 1]` converges
absolutely. -/
theorem summable_factorialSeries (hq0 : ∀ k, 0 ≤ q k) (hq1 : ∀ k, q k ≤ 1) (r : ℕ) {z : ℝ}
    (hz : |z| < 1) : Summable fun k => (k.descFactorial r : ℝ) * q k * z ^ (k - r) := by
  have hρ0 : 0 < (|z| + 1) / 2 := by positivity
  exact Summable.of_norm_bounded (summable_factorialSeries_bound hρ0 (by linarith) r)
    (factorialSeries_term_le hq0 hq1 hρ0 (by linarith) r)

/-- **Term by term differentiation**: inside the unit disk the derivative of the `r`-th
factorial series is the `(r + 1)`-th one. -/
theorem hasDerivAt_factorialSeries (hq0 : ∀ k, 0 ≤ q k) (hq1 : ∀ k, q k ≤ 1) (r : ℕ) {z : ℝ}
    (hz : |z| < 1) : HasDerivAt (factorialSeries q r) (factorialSeries q (r + 1) z) z := by
  set ρ := (|z| + 1) / 2 with hρ
  have hρ0 : 0 < ρ := by positivity
  have hρ1 : ρ < 1 := by linarith
  have hzρ : z ∈ Ioo (-ρ) ρ := abs_lt.mp (by linarith)
  have hle : ∀ y ∈ Ioo (-ρ) ρ, |y| ≤ ρ := fun y hy => abs_le.mpr ⟨hy.1.le, hy.2.le⟩
  refine hasDerivAt_tsum_of_isPreconnected (summable_factorialSeries_bound hρ0 hρ1 (r + 1))
    isOpen_Ioo isPreconnected_Ioo (fun k y _ => ?_)
    (fun k y hy => factorialSeries_term_le hq0 hq1 hρ0 (hle y hy) (r + 1) k) hzρ
    (summable_factorialSeries hq0 hq1 r hz) hzρ
  have h := (hasDerivAt_pow (k - r) y).const_mul ((k.descFactorial r : ℝ) * q k)
  convert h using 1
  rw [Nat.descFactorial_succ, Nat.cast_mul, Nat.sub_sub]
  ring

private lemma iteratedDeriv_eqOn_factorialSeries (hq0 : ∀ k, 0 ≤ q k) (hq1 : ∀ k, q k ≤ 1)
    {G : ℝ → ℝ} (hG : EqOn G (factorialSeries q 0) (Ioo (-1) 1)) (r : ℕ) :
    EqOn (iteratedDeriv r G) (factorialSeries q r) (Ioo (-1) 1) := by
  induction r with
  | zero => rw [iteratedDeriv_zero]; exact hG
  | succ r ih =>
    intro z hz
    rw [iteratedDeriv_succ, (eventuallyEq_of_mem (isOpen_Ioo.mem_nhds hz) ih).deriv_eq]
    exact (hasDerivAt_factorialSeries hq0 hq1 r (abs_lt.mpr hz)).deriv

theorem factorialSeries_zero (q : ℕ → ℝ) (z : ℝ) :
    factorialSeries q 0 z = ∑' k, q k * z ^ k := by
  simp only [factorialSeries, Nat.descFactorial_zero, Nat.cast_one, one_mul, Nat.sub_zero]

/-- At the origin the `r`-th factorial series is `r! q r`. -/
theorem factorialSeries_at_zero (q : ℕ → ℝ) (r : ℕ) :
    factorialSeries q r 0 = r.factorial * q r := by
  rw [factorialSeries, tsum_eq_single r]
  · rw [Nat.descFactorial_self, Nat.sub_self, pow_zero, mul_one]
  · intro k hk
    rcases lt_or_gt_of_ne hk with h | h
    · rw [Nat.descFactorial_eq_zero_iff_lt.mpr h, Nat.cast_zero, zero_mul, zero_mul]
    · rw [zero_pow (by omega), mul_zero]

private lemma tsum_eq_tsum_add_of_eq_zero {f : ℕ → ℝ} (r : ℕ) (hf : Summable f)
    (h0 : ∀ k < r, f k = 0) : ∑' k, f k = ∑' j, f (j + r) := by
  rw [← hf.sum_add_tsum_nat_add r, Finset.sum_eq_zero fun k hk => h0 k (Finset.mem_range.mp hk),
    zero_add]

/-- **Abel's theorem for the factorial series**: if `∑ k (k - 1) ⋯ (k - r + 1) q k` converges,
the `r`-th factorial series tends to its sum as `z ↑ 1`. -/
theorem tendsto_factorialSeries (hq0 : ∀ k, 0 ≤ q k) (hq1 : ∀ k, q k ≤ 1) (r : ℕ)
    (hsum : Summable fun k => (k.descFactorial r : ℝ) * q k) :
    Tendsto (factorialSeries q r) (𝓝[<] 1) (𝓝 (∑' k, (k.descFactorial r : ℝ) * q k)) := by
  have hz0 : ∀ k < r, (k.descFactorial r : ℝ) = 0 := fun k hk => by
    rw [Nat.descFactorial_eq_zero_iff_lt.mpr hk, Nat.cast_zero]
  set c : ℕ → ℝ := fun j => ((j + r).descFactorial r : ℝ) * q (j + r) with hc
  have hcs : Summable c := (summable_nat_add_iff r).mpr hsum
  have hlim := Real.tendsto_tsum_powerSeries_nhdsWithin_lt hcs.hasSum.tendsto_sum_nat
  rw [← tsum_eq_tsum_add_of_eq_zero r hsum fun k hk => by rw [hz0 k hk, zero_mul]] at hlim
  refine hlim.congr' (eventuallyEq_of_mem (Ioo_mem_nhdsLT (by norm_num : (-1 : ℝ) < 1)) ?_)
  intro z hz
  rw [factorialSeries, tsum_eq_tsum_add_of_eq_zero r
    (summable_factorialSeries hq0 hq1 r (abs_lt.mpr hz))
    fun k hk => by rw [hz0 k hk, zero_mul, zero_mul]]
  simp only [hc, Nat.add_sub_cancel]

/-- **The converse of Abel's theorem for nonnegative coefficients**: if the `r`-th factorial
series has a finite limit as `z ↑ 1`, the series `∑ k (k - 1) ⋯ (k - r + 1) q k` converges. -/
theorem summable_of_tendsto_factorialSeries (hq0 : ∀ k, 0 ≤ q k) (hq1 : ∀ k, q k ≤ 1)
    (r : ℕ) {L : ℝ} (h : Tendsto (factorialSeries q r) (𝓝[<] 1) (𝓝 L)) :
    Summable fun k => (k.descFactorial r : ℝ) * q k := by
  refine summable_of_sum_range_le (c := L) (fun k => mul_nonneg (Nat.cast_nonneg _) (hq0 k))
    fun N => ?_
  have hP : Tendsto (fun z : ℝ => ∑ k ∈ range N, (k.descFactorial r : ℝ) * q k * z ^ (k - r))
      (𝓝[<] 1) (𝓝 (∑ k ∈ range N, (k.descFactorial r : ℝ) * q k)) := by
    have hc : Continuous fun z : ℝ =>
        ∑ k ∈ range N, (k.descFactorial r : ℝ) * q k * z ^ (k - r) := by fun_prop
    have := (hc.tendsto 1).mono_left (nhdsWithin_le_nhds (s := Iio 1))
    simpa only [one_pow, mul_one] using this
  refine le_of_tendsto_of_tendsto hP h
    (eventually_of_mem (Ioo_mem_nhdsLT zero_lt_one) fun z hz => ?_)
  have hz' : |z| < 1 := by rw [abs_of_pos hz.1]; exact hz.2
  exact (summable_factorialSeries hq0 hq1 r hz').sum_le_tsum _
    fun k _ => mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (hq0 k)) (pow_nonneg hz.1.le _)

end Series

/-! ### Expectations under a law on `ℕ` -/

section Mass

variable (ν : Measure ℕ) [IsFiniteMeasure ν]

/-- **Integrability under a law on `ℕ`**: `g` is integrable exactly when `∑ ν{k} |g k|`
converges. -/
theorem integrable_iff_summable_mass (g : ℕ → ℝ) :
    Integrable g ν ↔ Summable fun k => ν.real {k} * |g k| := by
  conv_lhs => rw [← Measure.sum_smul_dirac ν]
  rw [integrable_sum_dirac_iff fun _ => measure_ne_top _ _]
  simp only [measureReal_def, Real.norm_eq_abs]

variable {ν} in
/-- **Expectations under a law on `ℕ` as series**: `∫ g dν = ∑ ν{k} g k` for integrable `g`. -/
theorem hasSum_integral_mass {g : ℕ → ℝ} (hg : Integrable g ν) :
    HasSum (fun k => ν.real {k} * g k) (∫ k, g k ∂ν) := by
  have hs : Summable fun k => ν.real {k} * g k :=
    Summable.of_norm (((integrable_iff_summable_mass ν g).1 hg).congr fun k => by
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg measureReal_nonneg])
  rw [integral_countable hg]
  simpa only [smul_eq_mul] using hs.hasSum

end Mass

/-! ### The generating function -/

section GeneratingFunction

/-- The **probability generating function** `G_ν(z) = ∫ z ^ k ν(dk)` of a law `ν` on `ℕ`. -/
noncomputable def generatingFunction (ν : Measure ℕ) (z : ℝ) : ℝ := ∫ k, z ^ k ∂ν

variable {ν : Measure ℕ} [IsProbabilityMeasure ν]

theorem integrable_pow_of_abs_le_one {z : ℝ} (hz : |z| ≤ 1) : Integrable (fun k : ℕ => z ^ k) ν :=
  (integrable_const (1 : ℝ)).mono' Measurable.of_discrete.aestronglyMeasurable
    (ae_of_all _ fun k => by rw [Real.norm_eq_abs, abs_pow]; exact pow_le_one₀ (abs_nonneg z) hz)

/-- **The generating function as a power series**: for `|z| ≤ 1`,
`G_ν(z) = ∑ ν{k} z ^ k`. -/
theorem hasSum_generatingFunction {z : ℝ} (hz : |z| ≤ 1) :
    HasSum (fun k => ν.real {k} * z ^ k) (generatingFunction ν z) :=
  hasSum_integral_mass (integrable_pow_of_abs_le_one hz)

theorem generatingFunction_one : generatingFunction ν 1 = 1 := by
  simp [generatingFunction]

/-- On the open unit disk the iterated derivatives of `G_ν` are the factorial series of the
mass function. -/
theorem iteratedDeriv_generatingFunction_eqOn (r : ℕ) :
    EqOn (iteratedDeriv r (generatingFunction ν)) (factorialSeries (fun k => ν.real {k}) r)
      (Ioo (-1) 1) := by
  refine iteratedDeriv_eqOn_factorialSeries (fun _ => measureReal_nonneg)
    (fun _ => measureReal_le_one) (fun z hz => ?_) r
  rw [factorialSeries_zero]
  exact (hasSum_generatingFunction (abs_le.mpr ⟨hz.1.le, hz.2.le⟩)).tsum_eq.symm

/-- **The generating function is smooth inside the unit disk**: for `|z| < 1`, its `r`-th
derivative is differentiable at `z` with derivative the `(r + 1)`-th derivative. -/
theorem hasDerivAt_iteratedDeriv_generatingFunction (r : ℕ) {z : ℝ} (hz : |z| < 1) :
    HasDerivAt (iteratedDeriv r (generatingFunction ν))
      (iteratedDeriv (r + 1) (generatingFunction ν) z) z := by
  have hzI : z ∈ Ioo (-1 : ℝ) 1 := abs_lt.mp hz
  have hev : iteratedDeriv r (generatingFunction ν) =ᶠ[𝓝 z]
      factorialSeries (fun k => ν.real {k}) r :=
    eventuallyEq_of_mem (isOpen_Ioo.mem_nhds hzI) (iteratedDeriv_generatingFunction_eqOn r)
  rw [iteratedDeriv_generatingFunction_eqOn (r + 1) hzI]
  exact (hasDerivAt_factorialSeries (fun _ => measureReal_nonneg)
    (fun _ => measureReal_le_one) r hz).congr_of_eventuallyEq hev

/-- **The mass function from the generating function**: `ν{k} = G_ν^(k)(0) / k!`. -/
theorem measureReal_singleton_eq_iteratedDeriv (k : ℕ) :
    ν.real {k} = iteratedDeriv k (generatingFunction ν) 0 / k.factorial := by
  rw [iteratedDeriv_generatingFunction_eqOn k ⟨by norm_num, by norm_num⟩,
    factorialSeries_at_zero,
    mul_div_cancel_left₀ _ (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero k))]

private lemma iteratedDeriv_eqOn_of_eqOn {G H : ℝ → ℝ} (h : EqOn G H (Ioo (-1) 1)) (r : ℕ) :
    EqOn (iteratedDeriv r G) (iteratedDeriv r H) (Ioo (-1) 1) := by
  induction r with
  | zero => simpa only [iteratedDeriv_zero] using h
  | succ r ih =>
    intro z hz
    rw [iteratedDeriv_succ, iteratedDeriv_succ,
      (eventuallyEq_of_mem (isOpen_Ioo.mem_nhds hz) ih).deriv_eq]

/-- **The generating function determines the law**: two probability laws on `ℕ` whose
generating functions agree on `(-1, 1)` are equal. -/
theorem eq_of_generatingFunction_eqOn {ν' : Measure ℕ} [IsProbabilityMeasure ν']
    (h : EqOn (generatingFunction ν) (generatingFunction ν') (Ioo (-1) 1)) : ν = ν' := by
  refine Measure.ext_of_singleton fun k => ?_
  have hk : ν.real {k} = ν'.real {k} := by
    rw [measureReal_singleton_eq_iteratedDeriv, measureReal_singleton_eq_iteratedDeriv,
      iteratedDeriv_eqOn_of_eqOn h k ⟨by norm_num, by norm_num⟩]
  rw [← ofReal_measureReal, hk, ofReal_measureReal]

private lemma integrable_descFactorial_iff (r : ℕ) :
    Integrable (fun k : ℕ => (k.descFactorial r : ℝ)) ν ↔
      Summable fun k => (k.descFactorial r : ℝ) * ν.real {k} := by
  rw [integrable_iff_summable_mass]
  simp only [Nat.abs_cast, mul_comm]

/-- **Factorial moments from the generating function**: if the factorial moment
`∫ k (k - 1) ⋯ (k - r + 1) dν` is finite, the `r`-th derivative of `G_ν` tends to it as
`z ↑ 1`. -/
theorem tendsto_iteratedDeriv_generatingFunction (r : ℕ)
    (hi : Integrable (fun k : ℕ => (k.descFactorial r : ℝ)) ν) :
    Tendsto (iteratedDeriv r (generatingFunction ν)) (𝓝[<] 1)
      (𝓝 (∫ k, (k.descFactorial r : ℝ) ∂ν)) := by
  have hev : iteratedDeriv r (generatingFunction ν) =ᶠ[𝓝[<] 1]
      factorialSeries (fun k => ν.real {k}) r :=
    eventuallyEq_of_mem (Ioo_mem_nhdsLT (by norm_num)) (iteratedDeriv_generatingFunction_eqOn r)
  have hval : ∫ k, (k.descFactorial r : ℝ) ∂ν =
      ∑' k, (k.descFactorial r : ℝ) * ν.real {k} := by
    rw [← (hasSum_integral_mass hi).tsum_eq]
    simp only [mul_comm]
  rw [hval]
  exact (tendsto_factorialSeries (fun _ => measureReal_nonneg) (fun _ => measureReal_le_one) r
    ((integrable_descFactorial_iff r).mp hi)).congr' hev.symm

/-- **A finite limit of the derivatives at one gives a finite factorial moment**: if the `r`-th
derivative of `G_ν` has the limit `L` as `z ↑ 1`, the factorial moment
`∫ k (k - 1) ⋯ (k - r + 1) dν` is finite and equals `L`. -/
theorem integrable_descFactorial_of_tendsto (r : ℕ) {L : ℝ}
    (h : Tendsto (iteratedDeriv r (generatingFunction ν)) (𝓝[<] 1) (𝓝 L)) :
    Integrable (fun k : ℕ => (k.descFactorial r : ℝ)) ν ∧
      ∫ k, (k.descFactorial r : ℝ) ∂ν = L := by
  have hev : iteratedDeriv r (generatingFunction ν) =ᶠ[𝓝[<] 1]
      factorialSeries (fun k => ν.real {k}) r :=
    eventuallyEq_of_mem (Ioo_mem_nhdsLT (by norm_num)) (iteratedDeriv_generatingFunction_eqOn r)
  have hi := (integrable_descFactorial_iff r).mpr (summable_of_tendsto_factorialSeries
    (fun _ => measureReal_nonneg) (fun _ => measureReal_le_one) r (h.congr' hev))
  exact ⟨hi, tendsto_nhds_unique (tendsto_iteratedDeriv_generatingFunction r hi) h⟩

end GeneratingFunction

/-! ### Counts as random variables -/

section RandomVariable

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- The generating function of the law of a count `X` is `E[z ^ X]`. -/
theorem generatingFunction_map {X : Ω → ℕ} (hX : Measurable X) (z : ℝ) :
    generatingFunction (μ.map X) z = ∫ ω, z ^ X ω ∂μ := by
  rw [generatingFunction, integral_map hX.aemeasurable Measurable.of_discrete.aestronglyMeasurable]

/-- **The generating function and the moment generating function**: `G(z) = M(log z)` for
`z > 0`. -/
theorem generatingFunction_map_eq_mgf {X : Ω → ℕ} (hX : Measurable X) {z : ℝ} (hz : 0 < z) :
    generatingFunction (μ.map X) z = mgf (fun ω => (X ω : ℝ)) μ (Real.log z) := by
  rw [generatingFunction_map hX, mgf]
  refine integral_congr_ae (ae_of_all _ fun ω => ?_)
  simp only
  rw [mul_comm, Real.exp_nat_mul, Real.exp_log hz]

/-- **The product rule for independent counts**: if `Y_i` are independent counts, the
generating function of `∑ Y_i` is the product of their generating functions, for `|z| ≤ 1`. -/
theorem generatingFunction_map_sum [IsProbabilityMeasure μ] {ι : Type*} [Fintype ι]
    {Y : ι → Ω → ℕ} (hY : ∀ i, Measurable (Y i)) (hind : iIndepFun Y μ) {z : ℝ}
    (hz : |z| ≤ 1) :
    Integrable (fun ω => z ^ ∑ i, Y i ω) μ ∧ generatingFunction (μ.map fun ω => ∑ i, Y i ω) z =
      ∏ i, generatingFunction (μ.map (Y i)) z := by
  refine ⟨(integrable_pow_of_abs_le_one (ν := μ.map fun ω => ∑ i, Y i ω) hz).comp_measurable
    (Finset.measurable_sum _ fun i _ => hY i), ?_⟩
  rw [generatingFunction_map (Finset.measurable_sum _ fun i _ => hY i)]
  simp only [generatingFunction_map (hY _)]
  have h := hind.integral_fun_prod_comp (f := fun _ (k : ℕ) => z ^ k)
    (fun i => (hY i).aemeasurable) (fun _ => Measurable.of_discrete.aestronglyMeasurable)
  simpa only [Finset.prod_pow_eq_pow_sum] using h

/-- **The product rule for two independent counts**: `G_{X + Y}(z) = G_X(z) G_Y(z)` for
`|z| ≤ 1`, where `z ^ (X + Y)` is integrable. -/
theorem generatingFunction_map_add [IsProbabilityMeasure μ] {X Y : Ω → ℕ} (hX : Measurable X)
    (hY : Measurable Y) (hXY : IndepFun X Y μ) {z : ℝ} (hz : |z| ≤ 1) :
    Integrable (fun ω => z ^ (X ω + Y ω)) μ ∧ generatingFunction (μ.map fun ω => X ω + Y ω) z =
      generatingFunction (μ.map X) z * generatingFunction (μ.map Y) z := by
  refine ⟨(integrable_pow_of_abs_le_one (ν := μ.map fun ω => X ω + Y ω) hz).comp_measurable
    (hX.add hY), ?_⟩
  rw [generatingFunction_map (μ := μ) (X := fun ω => X ω + Y ω) (hX.add hY),
    generatingFunction_map hX, generatingFunction_map hY]
  have hi : IndepFun (fun ω => z ^ X ω) (fun ω => z ^ Y ω) μ :=
    hXY.comp (φ := fun k : ℕ => z ^ k) (ψ := fun k : ℕ => z ^ k) Measurable.of_discrete
      Measurable.of_discrete
  simp only [pow_add]
  exact hi.integral_fun_mul_eq_mul_integral
    (Measurable.of_discrete.comp hX).aestronglyMeasurable
    (Measurable.of_discrete.comp hY).aestronglyMeasurable

end RandomVariable

end NetworkMetaRegression

end CausalInference
