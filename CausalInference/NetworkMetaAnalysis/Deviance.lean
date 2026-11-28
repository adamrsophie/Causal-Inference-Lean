/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import Mathlib.InformationTheory.KullbackLeibler.KLFun

/-!
# The binomial deviance

For an arm with `y` events out of `n` and event probability `p`, the binomial log likelihood
without the binomial coefficient is `ℓ(q) = y log q + (n - y) log (1 - q)` and the deviance
against the saturated model is
`D = 2 [y log (y / (n p)) + (n - y) log ((n - y) / (n (1 - p)))]`.

**The convention `0 log 0 = 0`.** In Mathlib `Real.log 0 = 0`, so `0 * Real.log t = 0` for every
`t`: a term with a zero count vanishes, which is the convention `0 log 0 = 0`. It is the right
value and not a junk one: the saturated log likelihood `ℓ(y / n)` at `y = 0` is the limit of
`ℓ(q)` as `q → 0⁺` (`tendsto_binomialLogLik_zero`) and at `y = n` the limit as `q → 1⁻`
(`tendsto_binomialLogLik_one`). All other statements assume `0 < p < 1` and `0 ≤ y ≤ n`.

* **The saturated model** (`binomialDeviance_eq`): `D = 2 [ℓ(y / n) - ℓ(p)]`.
* **The deviance as a divergence** (`binomialDeviance_eq_klFun`):
  `D = 2 [n p φ(y / (n p)) + n (1 - p) φ((n - y) / (n (1 - p)))]` with the Kullback Leibler
  function `φ(x) = x log x + 1 - x ≥ 0`.
* **Nonnegativity and the equality case** (`binomialDeviance_nonneg`,
  `binomialDeviance_eq_zero_iff`): `D ≥ 0`, with `D = 0` iff `p = y / n`; so `y / n` is the
  unique maximizer of the likelihood over `(0, 1)` when `0 < y < n`, and the supremum otherwise
  (`binomialLogLik_le_saturated`).
* **The residual deviance** of a network (`residualDeviance`), the sum over arms: nonnegative,
  and zero iff every fitted probability is the observed proportion.

## Main definitions

* `binomialLogLik`, `binomialDeviance`, `residualDeviance`.

## Main results

* `binomialLogLik_saturated_zero`, `binomialLogLik_saturated_self`,
  `tendsto_binomialLogLik_zero`, `tendsto_binomialLogLik_one`.
* `mul_log_div_eq_klFun`, `binomialDeviance_eq`, `binomialDeviance_eq_klFun`,
  `binomialDeviance_nonneg`, `binomialDeviance_eq_zero_iff`, `binomialLogLik_le_saturated`.
* `residualDeviance_nonneg`, `residualDeviance_eq_zero_iff`.

## References

* D. J. Spiegelhalter, N. G. Best, B. P. Carlin and A. van der Linde, *Bayesian measures of
  model complexity and fit*, Journal of the Royal Statistical Society B 64 (2002).
-/

@[expose] public section

namespace CausalInference

namespace NetworkMetaAnalysis

open Real Filter Topology InformationTheory

/-- The **binomial log likelihood** of `y` events out of `n` at probability `q`, without the
binomial coefficient: `y log q + (n - y) log (1 - q)`. -/
noncomputable def binomialLogLik (n y q : ℝ) : ℝ := y * log q + (n - y) * log (1 - q)

/-- The **binomial deviance** of `y` events out of `n` at the fitted probability `p`, against
the saturated model. -/
noncomputable def binomialDeviance (n y p : ℝ) : ℝ :=
  2 * (y * log (y / (n * p)) + (n - y) * log ((n - y) / (n * (1 - p))))

/-! ### The convention `0 log 0 = 0` -/

/-- With no events the saturated log likelihood is `0`. -/
theorem binomialLogLik_saturated_zero (n : ℝ) : binomialLogLik n 0 (0 / n) = 0 := by
  simp [binomialLogLik]

/-- With only events the saturated log likelihood is `0`. -/
theorem binomialLogLik_saturated_self {n : ℝ} (hn : n ≠ 0) : binomialLogLik n n (n / n) = 0 := by
  simp [binomialLogLik, div_self hn]

/-- **The convention is the limit at `y = 0`**: `ℓ(q) → ℓ(0)` as `q → 0`. -/
theorem tendsto_binomialLogLik_zero (n : ℝ) :
    Tendsto (binomialLogLik n 0) (𝓝 0) (𝓝 (binomialLogLik n 0 0)) := by
  have hc : ContinuousAt (fun q : ℝ => (n - 0) * log (1 - q)) 0 :=
    continuousAt_const.mul ((continuousAt_const.sub continuousAt_id).log (by norm_num))
  have e : binomialLogLik n 0 = fun q => (n - 0) * log (1 - q) := by
    funext q
    simp [binomialLogLik]
  rw [e]
  exact hc.tendsto

/-- **The convention is the limit at `y = n`**: `ℓ(q) → ℓ(1)` as `q → 1`. -/
theorem tendsto_binomialLogLik_one (n : ℝ) :
    Tendsto (binomialLogLik n n) (𝓝 1) (𝓝 (binomialLogLik n n 1)) := by
  have hc : ContinuousAt (fun q : ℝ => n * log q) 1 :=
    continuousAt_const.mul (continuousAt_id.log (by norm_num))
  have e : binomialLogLik n n = fun q => n * log q := by
    funext q
    simp [binomialLogLik]
  rw [e]
  exact hc.tendsto

/-! ### The deviance against the saturated model -/

/-- `u log (u / v) = v φ(u / v) + u - v` with the Kullback Leibler function `φ`, for `v ≠ 0`
(also at `u = 0`). -/
theorem mul_log_div_eq_klFun (u : ℝ) {v : ℝ} (hv : v ≠ 0) :
    u * log (u / v) = v * klFun (u / v) + u - v := by
  rw [klFun_apply]
  field_simp
  ring

theorem mul_log_div_mul_eq {u v w : ℝ} (hv : v ≠ 0) (hw : w ≠ 0) :
    u * log (u / (v * w)) = u * log (u / v) - u * log w := by
  by_cases hu : u = 0
  · simp [hu]
  · rw [← div_div, log_div (div_ne_zero hu hv) hw]
    ring

/-- **The deviance is twice the saturated minus the fitted log likelihood.** -/
theorem binomialDeviance_eq {n y p : ℝ} (hn : 0 < n) (hp0 : 0 < p) (hp1 : p < 1) :
    binomialDeviance n y p = 2 * (binomialLogLik n y (y / n) - binomialLogLik n y p) := by
  have h1y : 1 - y / n = (n - y) / n := by field_simp
  rw [binomialDeviance, mul_log_div_mul_eq hn.ne' hp0.ne',
    mul_log_div_mul_eq hn.ne' (by linarith : 1 - p ≠ 0), binomialLogLik, binomialLogLik, h1y]
  ring

/-- **The deviance as a divergence**:
`D = 2 [n p φ(y / (n p)) + n (1 - p) φ((n - y) / (n (1 - p)))]`. -/
theorem binomialDeviance_eq_klFun {n y p : ℝ} (hn : 0 < n) (hp0 : 0 < p) (hp1 : p < 1) :
    binomialDeviance n y p =
      2 * (n * p * klFun (y / (n * p)) + n * (1 - p) * klFun ((n - y) / (n * (1 - p)))) := by
  have h1 : n * p ≠ 0 := (mul_pos hn hp0).ne'
  have h2 : n * (1 - p) ≠ 0 := (mul_pos hn (by linarith)).ne'
  rw [binomialDeviance, mul_log_div_eq_klFun y h1, mul_log_div_eq_klFun (n - y) h2]
  ring

/-- **The deviance is nonnegative.** -/
theorem binomialDeviance_nonneg {n y p : ℝ} (hn : 0 < n) (hy0 : 0 ≤ y) (hyn : y ≤ n)
    (hp0 : 0 < p) (hp1 : p < 1) : 0 ≤ binomialDeviance n y p := by
  have h1 : 0 < n * p := mul_pos hn hp0
  have h2 : 0 < n * (1 - p) := mul_pos hn (by linarith)
  rw [binomialDeviance_eq_klFun hn hp0 hp1]
  have k1 := klFun_nonneg (div_nonneg hy0 h1.le)
  have k2 := klFun_nonneg (div_nonneg (by linarith : 0 ≤ n - y) h2.le)
  have := mul_nonneg h1.le k1
  have := mul_nonneg h2.le k2
  linarith

/-- **The equality case**: the deviance vanishes iff the fitted probability is the observed
proportion `y / n`. -/
theorem binomialDeviance_eq_zero_iff {n y p : ℝ} (hn : 0 < n) (hy0 : 0 ≤ y) (hyn : y ≤ n)
    (hp0 : 0 < p) (hp1 : p < 1) : binomialDeviance n y p = 0 ↔ p = y / n := by
  have h1 : 0 < n * p := mul_pos hn hp0
  have h2 : 0 < n * (1 - p) := mul_pos hn (by linarith)
  have k1 := klFun_nonneg (div_nonneg hy0 h1.le)
  have k2 := klFun_nonneg (div_nonneg (by linarith : 0 ≤ n - y) h2.le)
  have m1 := mul_nonneg h1.le k1
  have m2 := mul_nonneg h2.le k2
  rw [binomialDeviance_eq_klFun hn hp0 hp1]
  constructor
  · intro h
    have hz : n * p * klFun (y / (n * p)) = 0 := by linarith
    rcases mul_eq_zero.1 hz with h' | h'
    · exact absurd h' h1.ne'
    · rw [klFun_eq_zero_iff (div_nonneg hy0 h1.le), div_eq_one_iff_eq h1.ne'] at h'
      field_simp
      linarith
  · intro h
    have e1 : y / (n * p) = 1 := by
      rw [div_eq_one_iff_eq h1.ne', h]
      field_simp
    have e2 : (n - y) / (n * (1 - p)) = 1 := by
      rw [div_eq_one_iff_eq h2.ne', h]
      field_simp
    rw [e1, e2, klFun_one]
    ring

/-- **The saturated fit maximizes the likelihood**: `ℓ(q) ≤ ℓ(y / n)` for every `q ∈ (0, 1)`,
with equality iff `q = y / n`. -/
theorem binomialLogLik_le_saturated {n y q : ℝ} (hn : 0 < n) (hy0 : 0 ≤ y) (hyn : y ≤ n)
    (hq0 : 0 < q) (hq1 : q < 1) :
    binomialLogLik n y q ≤ binomialLogLik n y (y / n) ∧
      (binomialLogLik n y q = binomialLogLik n y (y / n) ↔ q = y / n) := by
  have h := binomialDeviance_nonneg hn hy0 hyn hq0 hq1
  have hz := binomialDeviance_eq_zero_iff hn hy0 hyn hq0 hq1
  rw [binomialDeviance_eq hn hq0 hq1] at h hz
  refine ⟨by linarith, ?_⟩
  rw [← hz]
  constructor <;> intro h' <;> linarith

/-! ### The residual deviance of a network -/

/-- The **residual deviance** of a network of arms: the sum of the arm deviances. -/
noncomputable def residualDeviance {A : Type*} [Fintype A] (n y p : A → ℝ) : ℝ :=
  ∑ a, binomialDeviance (n a) (y a) (p a)

theorem residualDeviance_nonneg {A : Type*} [Fintype A] {n y p : A → ℝ} (hn : ∀ a, 0 < n a)
    (hy0 : ∀ a, 0 ≤ y a) (hyn : ∀ a, y a ≤ n a) (hp0 : ∀ a, 0 < p a) (hp1 : ∀ a, p a < 1) :
    0 ≤ residualDeviance n y p :=
  Finset.sum_nonneg fun a _ => binomialDeviance_nonneg (hn a) (hy0 a) (hyn a) (hp0 a) (hp1 a)

/-- The residual deviance vanishes iff every fitted probability is the observed proportion. -/
theorem residualDeviance_eq_zero_iff {A : Type*} [Fintype A] {n y p : A → ℝ}
    (hn : ∀ a, 0 < n a) (hy0 : ∀ a, 0 ≤ y a) (hyn : ∀ a, y a ≤ n a) (hp0 : ∀ a, 0 < p a)
    (hp1 : ∀ a, p a < 1) : residualDeviance n y p = 0 ↔ ∀ a, p a = y a / n a := by
  rw [residualDeviance, Finset.sum_eq_zero_iff_of_nonneg fun a _ =>
    binomialDeviance_nonneg (hn a) (hy0 a) (hyn a) (hp0 a) (hp1 a)]
  simp only [Finset.mem_univ, true_imp_iff]
  exact forall_congr' fun a =>
    binomialDeviance_eq_zero_iff (hn a) (hy0 a) (hyn a) (hp0 a) (hp1 a)

end NetworkMetaAnalysis

end CausalInference
