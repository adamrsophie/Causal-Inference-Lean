/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.MetaAnalysis.CochranQLaw

/-!
# Meta-analysis: Egger's regression test

**Egger's regression** fits, by ordinary least squares, the standardized effects `zᵢ = yᵢ / sᵢ`
on the precisions `pᵢ = 1 / sᵢ`, `sᵢ > 0` the standard errors: `zᵢ ≈ α + β pᵢ`. Under the
common effect model `Yᵢ ~ N(θ, sᵢ²)` one has `zᵢ = θ pᵢ + uᵢ` with standard Gaussian errors, so
the true intercept is `0`; small study effects (funnel plot asymmetry) show up as a nonzero
intercept. The test statistic is the intercept divided by its estimated standard error.

**Simple linear regression.** For a regressor `x` and a response `z` on `k` points, with means
`x̄, z̄` and `Sₓₓ = ∑ (xᵢ - x̄)²`, the least squares slope is `β̂ = ∑ (xᵢ - x̄) zᵢ / Sₓₓ`, the
intercept `α̂ = z̄ - β̂ x̄` (`regSlope`, `regIntercept`), the residual sum of squares
`RSS = ∑ (zᵢ - α̂ - β̂ xᵢ)²` (`regRSS`), and the `t` statistic of the intercept is
`α̂ / √(RSS / (k - 2) · (1 / k + x̄² / Sₓₓ))` (`regInterceptStat`). The pair `(α̂, β̂)` minimizes
`∑ (zᵢ - α - β xᵢ)²` (`regRSS_le`).

**Egger's test** (Egger et al. 1997): the Egger intercept and statistic are those of the
regression of `z` on `p` (`eggerIntercept`, `eggerStat`).

* **The exact null law** (`hasLaw_eggerStat`): if the estimates are independent with
  `Yᵢ ~ N(θ, σ² sᵢ²)`, `σ² > 0`, from `k = m + 2` studies with `m ≥ 1`, and two standard errors
  differ, then the Egger statistic has the exact law `tₘ = t_{k-2}`; in the Gaussian common
  effect model (`σ² = 1`) this is `IsGaussianCommonEffectModel.hasLaw_eggerStat`. Proof: the
  intercept is `⟪a, z⟫` for a vector `a` orthogonal to `p`, the residual sum of squares is the
  squared length of the projection of the errors on the orthogonal complement of
  `span {a, p}`, and the `t` ratio of orthonormal coordinates of a standard Gaussian vector has
  the law `tₘ` (`stdGaussian_map_tStat`).
* **Two forms of the regression** (`eggerObj_eq_weightedObj`): the Egger least squares
  objective at `(α, β)` equals the precision weighted objective `∑ (yᵢ - β - α sᵢ)² / sᵢ²` of the
  regression of the effect on its standard error at intercept `β` and slope `α`: the Egger
  intercept is the weighted slope on the standard error.

## Main definitions

* `regMean`, `regSxx`, `regSlope`, `regIntercept`, `regRSS`, `regInterceptStat`.
* `eggerObj`, `eggerWeightedObj`, `eggerIntercept`, `eggerStat`.

## Main results

* `regIntercept_eq_sum`, `sum_regInterceptCoef_mul`, `sum_regInterceptCoef_sq`,
  `regRSS_eq`, `regRSS_le`.
* `map_stdGaussian_regInterceptStat`, `hasLaw_eggerStat`,
  `IsGaussianCommonEffectModel.hasLaw_eggerStat`, `eggerObj_eq_weightedObj`.

## References

* M. Egger, G. Davey Smith, M. Schneider and C. Minder, *Bias in meta-analysis detected by a
  simple, graphical test*, BMJ 315 (1997).
-/

@[expose] public section

namespace CausalInference

namespace MetaAnalysis

open MeasureTheory ProbabilityTheory Finset
open scoped RealInnerProductSpace

/-! ### Simple linear regression -/

section Regression

variable {ι : Type*} [Fintype ι]

/-- The mean `x̄ = ∑ xᵢ / k`. -/
noncomputable def regMean (x : ι → ℝ) : ℝ := (∑ i, x i) / Fintype.card ι

/-- `Sₓₓ = ∑ (xᵢ - x̄)²`. -/
noncomputable def regSxx (x : ι → ℝ) : ℝ := ∑ i, (x i - regMean x) ^ 2

/-- The least squares slope `β̂ = ∑ (xᵢ - x̄) zᵢ / Sₓₓ`. -/
noncomputable def regSlope (x z : ι → ℝ) : ℝ := (∑ i, (x i - regMean x) * z i) / regSxx x

/-- The least squares intercept `α̂ = z̄ - β̂ x̄`. -/
noncomputable def regIntercept (x z : ι → ℝ) : ℝ := regMean z - regSlope x z * regMean x

/-- The residual sum of squares `RSS = ∑ (zᵢ - α̂ - β̂ xᵢ)²`. -/
noncomputable def regRSS (x z : ι → ℝ) : ℝ :=
  ∑ i, (z i - regIntercept x z - regSlope x z * x i) ^ 2

/-- The `t` statistic of the intercept, `α̂ / √(RSS / (k - 2) · (1 / k + x̄² / Sₓₓ))`. -/
noncomputable def regInterceptStat (x z : ι → ℝ) : ℝ :=
  regIntercept x z / √(regRSS x z / ((Fintype.card ι : ℝ) - 2) *
    (1 / Fintype.card ι + regMean x ^ 2 / regSxx x))

/-- The coefficients `aᵢ = 1 / k - x̄ (xᵢ - x̄) / Sₓₓ` of the intercept, `α̂ = ∑ aᵢ zᵢ`. -/
noncomputable def regInterceptCoef (x : ι → ℝ) (i : ι) : ℝ :=
  1 / Fintype.card ι - regMean x * (x i - regMean x) / regSxx x

variable {x : ι → ℝ}

theorem sum_sub_regMean [Nonempty ι] (x : ι → ℝ) : ∑ i, (x i - regMean x) = 0 := by
  have hk : (Fintype.card ι : ℝ) ≠ 0 := by positivity
  rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, regMean,
    mul_div_cancel₀ _ hk, sub_self]

theorem sum_sub_regMean_mul_self [Nonempty ι] (x : ι → ℝ) :
    ∑ i, (x i - regMean x) * x i = regSxx x := by
  have h := sum_sub_regMean x
  have : ∀ i, (x i - regMean x) * x i = (x i - regMean x) ^ 2 + regMean x * (x i - regMean x) :=
    fun i => by ring
  rw [regSxx, Finset.sum_congr rfl fun i _ => this i, Finset.sum_add_distrib, ← Finset.mul_sum,
    h, mul_zero, add_zero]

/-- **The intercept is linear in the response**: `α̂ = ∑ aᵢ zᵢ`. -/
theorem regIntercept_eq_sum (x z : ι → ℝ) :
    regIntercept x z = ∑ i, regInterceptCoef x i * z i := by
  simp only [regIntercept, regSlope, regMean, regInterceptCoef, sub_mul, Finset.sum_sub_distrib,
    div_mul_eq_mul_div, ← Finset.sum_div, mul_assoc, ← Finset.mul_sum, one_mul]
  ring

/-- `∑ aᵢ xᵢ = 0`: the intercept does not respond to the regressor. -/
theorem sum_regInterceptCoef_mul [Nonempty ι] (hS : regSxx x ≠ 0) :
    ∑ i, regInterceptCoef x i * x i = 0 := by
  rw [← regIntercept_eq_sum, regIntercept, regSlope, sum_sub_regMean_mul_self, div_self hS,
    one_mul, sub_self]

/-- `∑ aᵢ = 1`. -/
theorem sum_regInterceptCoef [Nonempty ι] : ∑ i, regInterceptCoef x i = 1 := by
  have hk : (Fintype.card ι : ℝ) ≠ 0 := by positivity
  have h := regIntercept_eq_sum x (fun _ => 1)
  simp only [mul_one] at h
  rw [← h, regIntercept, regSlope]
  simp only [mul_one]
  rw [sum_sub_regMean x, zero_div, zero_mul, sub_zero, regMean]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
  exact div_self hk

/-- `∑ aᵢ² = 1 / k + x̄² / Sₓₓ`: the squared length of the intercept coefficients. -/
theorem sum_regInterceptCoef_sq [Nonempty ι] (hS : regSxx x ≠ 0) :
    ∑ i, regInterceptCoef x i ^ 2 = 1 / Fintype.card ι + regMean x ^ 2 / regSxx x := by
  have hk : (Fintype.card ι : ℝ) ≠ 0 := by positivity
  have h0 := sum_sub_regMean x
  have hexp : ∀ i, regInterceptCoef x i ^ 2 = (1 / Fintype.card ι) ^ 2 -
      2 * (1 / Fintype.card ι) * (regMean x / regSxx x) * (x i - regMean x) +
        (regMean x / regSxx x) ^ 2 * (x i - regMean x) ^ 2 := fun i => by
    simp only [regInterceptCoef]; ring
  rw [Finset.sum_congr rfl fun i _ => hexp i]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, h0,
    Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [← regSxx]
  field_simp
  ring

theorem regSxx_nonneg (x : ι → ℝ) : 0 ≤ regSxx x :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

/-- **Residuals of a shifted and scaled response**: `RSS(c x + σ z) = σ² RSS(z)`. -/
theorem regRSS_add_smul [Nonempty ι] (hS : regSxx x ≠ 0) (c σ : ℝ) (z : ι → ℝ) :
    regRSS x (fun i => c * x i + σ * z i) = σ ^ 2 * regRSS x z := by
  have hslope : regSlope x (fun i => c * x i + σ * z i) = c + σ * regSlope x z := by
    simp only [regSlope, mul_add, Finset.sum_add_distrib]
    have h1 : ∑ i, (x i - regMean x) * (c * x i) = c * regSxx x := by
      rw [← sum_sub_regMean_mul_self, Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by ring
    have h2 : ∑ i, (x i - regMean x) * (σ * z i) = σ * ∑ i, (x i - regMean x) * z i := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [h1, h2]
    field_simp
  have hint : regIntercept x (fun i => c * x i + σ * z i) = σ * regIntercept x z := by
    rw [regIntercept_eq_sum, regIntercept_eq_sum, Finset.mul_sum]
    have : ∀ i, regInterceptCoef x i * (c * x i + σ * z i) =
        c * (regInterceptCoef x i * x i) + σ * (regInterceptCoef x i * z i) := fun i => by ring
    rw [Finset.sum_congr rfl fun i _ => this i, Finset.sum_add_distrib, ← Finset.mul_sum,
      ← Finset.mul_sum, sum_regInterceptCoef_mul hS, mul_zero, zero_add]
  rw [regRSS, regRSS, hslope, hint, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

/-- **The residual sum of squares through an orthogonal basis of the fit**: with `aᵢ` the
intercept coefficients (orthogonal to `x`),
`RSS = ∑ zᵢ² - (∑ aᵢ zᵢ)² / ∑ aᵢ² - (∑ xᵢ zᵢ)² / ∑ xᵢ²`. -/
theorem regRSS_eq [Nonempty ι] (hS : regSxx x ≠ 0) (z : ι → ℝ) :
    regRSS x z = ∑ i, z i ^ 2 - (∑ i, regInterceptCoef x i * z i) ^ 2 /
      (∑ i, regInterceptCoef x i ^ 2) - (∑ i, x i * z i) ^ 2 / ∑ i, x i ^ 2 := by
  have hk : (Fintype.card ι : ℝ) ≠ 0 := by positivity
  have hSpos : 0 < regSxx x := lt_of_le_of_ne (regSxx_nonneg x) (Ne.symm hS)
  have hx : ∑ i, x i = (Fintype.card ι : ℝ) * regMean x := by rw [regMean]; field_simp
  have hz : ∑ i, z i = (Fintype.card ι : ℝ) * regMean z := by rw [regMean]; field_simp
  have hP : ∑ i, x i ^ 2 = regSxx x + (Fintype.card ι : ℝ) * regMean x ^ 2 := by
    have : ∀ i, x i ^ 2 = (x i - regMean x) ^ 2 + 2 * regMean x * (x i - regMean x) +
        regMean x ^ 2 := fun i => by ring
    rw [Finset.sum_congr rfl fun i _ => this i, Finset.sum_add_distrib, Finset.sum_add_distrib,
      ← Finset.mul_sum, sum_sub_regMean, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
      regSxx]
    ring
  have hxz : ∑ i, x i * z i = (∑ i, (x i - regMean x) * z i) + regMean x * ∑ i, z i := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  have hPpos : 0 < regSxx x + (Fintype.card ι : ℝ) * regMean x ^ 2 := by positivity
  have hexp : regRSS x z = ∑ i, z i ^ 2 - 2 * regIntercept x z * ∑ i, z i -
      2 * regSlope x z * ∑ i, x i * z i + (Fintype.card ι : ℝ) * regIntercept x z ^ 2 +
      2 * regIntercept x z * regSlope x z * ∑ i, x i + regSlope x z ^ 2 * ∑ i, x i ^ 2 := by
    rw [regRSS]
    have : ∀ i, (z i - regIntercept x z - regSlope x z * x i) ^ 2 = z i ^ 2 -
        2 * regIntercept x z * z i - 2 * regSlope x z * (x i * z i) + regIntercept x z ^ 2 +
        2 * regIntercept x z * regSlope x z * x i + regSlope x z ^ 2 * x i ^ 2 := fun i => by
      ring
    rw [Finset.sum_congr rfl fun i _ => this i]
    simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
      Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [hexp, ← regIntercept_eq_sum, sum_regInterceptCoef_sq hS, hP, hxz, hx, hz]
  have hα : regIntercept x z = regMean z - regSlope x z * regMean x := rfl
  have hβ : regSlope x z = (∑ i, (x i - regMean x) * z i) / regSxx x := rfl
  rw [hα, hβ]
  field_simp
  ring

/-- **The least squares property**: `(α̂, β̂)` minimizes `∑ (zᵢ - α - β xᵢ)²` when `Sₓₓ ≠ 0`. -/
theorem regRSS_le [Nonempty ι] (hS : regSxx x ≠ 0) (z : ι → ℝ) (α β : ℝ) :
    regRSS x z ≤ ∑ i, (z i - α - β * x i) ^ 2 := by
  have hk : (Fintype.card ι : ℝ) ≠ 0 := by positivity
  have hSpos : 0 < regSxx x := lt_of_le_of_ne (regSxx_nonneg x) (Ne.symm hS)
  set a := regIntercept x z
  set b := regSlope x z
  set r : ι → ℝ := fun i => z i - a - b * x i with hr
  have hr0 : ∑ i, r i = 0 := by
    have h := regIntercept_eq_sum x z
    simp only [hr, Finset.sum_sub_distrib, ← Finset.mul_sum, a, b, regIntercept, regSlope,
      regMean]
    rw [show ∑ i, x i = Fintype.card ι * ((∑ i, x i) / Fintype.card ι) by field_simp]
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    field_simp
    ring
  have hr1 : ∑ i, r i * x i = 0 := by
    have hrx : ∑ i, r i * x i = ∑ i, r i * (x i - regMean x) := by
      have : ∑ i, r i * (x i - regMean x) = ∑ i, r i * x i - regMean x * ∑ i, r i := by
        rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl fun i _ => by ring
      rw [this, hr0, mul_zero, sub_zero]
    rw [hrx]
    have : ∀ i, r i * (x i - regMean x) = (x i - regMean x) * z i -
        b * ((x i - regMean x) * x i) - a * (x i - regMean x) := fun i => by simp only [hr]; ring
    rw [Finset.sum_congr rfl fun i _ => this i, Finset.sum_sub_distrib, Finset.sum_sub_distrib,
      ← Finset.mul_sum, ← Finset.mul_sum, sum_sub_regMean, sum_sub_regMean_mul_self]
    simp only [b, regSlope]
    field_simp
    ring
  have hdec : ∑ i, (z i - α - β * x i) ^ 2 =
      regRSS x z + ∑ i, ((a - α) + (b - β) * x i) ^ 2 := by
    have : ∀ i, (z i - α - β * x i) ^ 2 = r i ^ 2 + 2 * (a - α) * r i +
        2 * (b - β) * (r i * x i) + ((a - α) + (b - β) * x i) ^ 2 := fun i => by
      simp only [hr]; ring
    rw [Finset.sum_congr rfl fun i _ => this i]
    simp only [Finset.sum_add_distrib, ← Finset.mul_sum, hr0, hr1, mul_zero, add_zero]
    rfl
  rw [hdec]
  exact le_add_of_nonneg_right (Finset.sum_nonneg fun i _ => sq_nonneg _)

end Regression

/-! ### The exact null law of the intercept statistic -/

section Law

variable {ι : Type*} [Fintype ι] {x : ι → ℝ}

/-- `⟪toLp f, Z⟫ = ∑ fᵢ Zᵢ`. -/
theorem inner_toLp_eq_sum (f : ι → ℝ) (Z : EuclideanSpace ℝ ι) :
    ⟪(WithLp.toLp 2 f : EuclideanSpace ℝ ι), Z⟫ = ∑ i, f i * Z i := by
  simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial]
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

/-- **The intercept statistic of a pure noise response has the law `tₘ`.** Let `k = m + 2`,
`m ≥ 1`, `Sₓₓ ≠ 0`, `σ > 0`, and `Z ~ N(0, I)`. For the response `zᵢ = c xᵢ + σ Zᵢ` (true
intercept `0`), the `t` statistic of the intercept has the law `tₘ`. Proof: with `aᵢ` the
intercept coefficients, `a ⟂ x`; the unit vectors `a / ‖a‖` and `x / ‖x‖` extend to an
orthonormal basis `b` of `ℝ^ι`, the statistic is `⟪b₀, Z⟫ / √(∑_{j ≥ 2} ⟪bⱼ, Z⟫² / m)`, and
`stdGaussian_map_tStat` applies. -/
theorem map_stdGaussian_regInterceptStat {m : ℕ} (hcard : Fintype.card ι = m + 2) (hm : 1 ≤ m)
    (hS : regSxx x ≠ 0) (c : ℝ) {σ : ℝ} (hσ : 0 < σ) :
    (stdGaussian (EuclideanSpace ℝ ι)).map
      (fun Z => regInterceptStat x fun i => c * x i + σ * Z i) = studentT m := by
  have : Nonempty ι := Fintype.card_pos_iff.1 (by omega)
  have hSpos : 0 < regSxx x := lt_of_le_of_ne (regSxx_nonneg x) (Ne.symm hS)
  set a := regInterceptCoef x with ha
  have hA : 0 < ∑ i, a i ^ 2 := by
    rw [sum_regInterceptCoef_sq hS]; positivity
  have hX : 0 < ∑ i, x i ^ 2 := by
    rcases (Finset.sum_nonneg fun i (_ : i ∈ Finset.univ) => sq_nonneg (x i)).lt_or_eq with
      h | h
    · exact h
    · exfalso
      have h0 : ∀ i, x i = 0 := fun i => pow_eq_zero_iff two_ne_zero |>.1
        ((Finset.sum_eq_zero_iff_of_nonneg fun j _ => sq_nonneg (x j)).1 h.symm i
          (Finset.mem_univ i))
      apply hS
      simp [regSxx, regMean, h0]
  set r := √(∑ i, a i ^ 2) with hr
  set q := √(∑ i, x i ^ 2) with hq
  have hr0 : 0 < r := Real.sqrt_pos.2 hA
  have hq0 : 0 < q := Real.sqrt_pos.2 hX
  set f1 : EuclideanSpace ℝ ι := WithLp.toLp 2 fun i => a i / r with hf1
  set f2 : EuclideanSpace ℝ ι := WithLp.toLp 2 fun i => x i / q with hf2
  have hr2 : r ^ 2 = ∑ i, a i ^ 2 := Real.sq_sqrt hA.le
  have hq2 : q ^ 2 = ∑ i, x i ^ 2 := Real.sq_sqrt hX.le
  have hax : ∑ i, a i * x i = 0 := sum_regInterceptCoef_mul hS
  have hf1f1 : ⟪f1, f1⟫ = 1 := by
    rw [hf1, inner_toLp_eq_sum]
    change ∑ i, a i / r * (a i / r) = 1
    rw [show ∑ i, a i / r * (a i / r) = (∑ i, a i ^ 2) / r ^ 2 by
      rw [Finset.sum_div]; exact Finset.sum_congr rfl fun i _ => by ring, hr2, div_self hA.ne']
  have hf2f2 : ⟪f2, f2⟫ = 1 := by
    rw [hf2, inner_toLp_eq_sum]
    change ∑ i, x i / q * (x i / q) = 1
    rw [show ∑ i, x i / q * (x i / q) = (∑ i, x i ^ 2) / q ^ 2 by
      rw [Finset.sum_div]; exact Finset.sum_congr rfl fun i _ => by ring, hq2, div_self hX.ne']
  have hf1f2 : ⟪f1, f2⟫ = 0 := by
    rw [hf1, inner_toLp_eq_sum]
    change ∑ i, a i / r * (x i / q) = 0
    rw [show ∑ i, a i / r * (x i / q) = (∑ i, a i * x i) / (r * q) by
      rw [Finset.sum_div]; exact Finset.sum_congr rfl fun i _ => by ring, hax, zero_div]
  have hf2f1 : ⟪f2, f1⟫ = 0 := by rw [real_inner_comm, hf1f2]
  have hn1 : ‖f1‖ = 1 := by
    have h := hf1f1
    rw [real_inner_self_eq_norm_sq] at h
    nlinarith [norm_nonneg f1]
  have hn2 : ‖f2‖ = 1 := by
    have h := hf2f2
    rw [real_inner_self_eq_norm_sq] at h
    nlinarith [norm_nonneg f2]
  set w : Fin (m + 2) → EuclideanSpace ℝ ι := fun j => if j = 0 then f1 else f2 with hw
  have h01 : (1 : Fin (m + 2)) ≠ 0 := Fin.zero_lt_one.ne'
  have hon : Orthonormal ℝ (({0, 1} : Set (Fin (m + 2))).domRestrict w) := by
    rw [orthonormal_iff_ite]
    rintro ⟨i, hi⟩ ⟨j, hj⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hi hj
    rcases hi with rfl | rfl <;> rcases hj with rfl | rfl <;>
      simp [Set.domRestrict, hw, h01, hn1, hn2, hf1f2, hf2f1]
  obtain ⟨b, hb⟩ := hon.exists_orthonormalBasis_extension_of_card_eq
    (by simp [hcard]) (v := w) (s := {0, 1})
  have hb0 : b 0 = f1 := by rw [hb 0 (by simp)]; simp [hw]
  have hb1 : b 1 = f2 := by rw [hb 1 (by simp)]; simp [hw, h01]
  set b' : Fin m → EuclideanSpace ℝ ι := fun j => b j.succ.succ with hb'
  have hcons : (Fin.cons (b 0) b' : Fin (m + 1) → EuclideanSpace ℝ ι) =
      b ∘ (Fin.cons 0 fun j : Fin m => j.succ.succ : Fin (m + 1) → Fin (m + 2)) := by
    funext j
    refine Fin.cases ?_ (fun j => ?_) j <;> simp [hb']
  have hinj : Function.Injective
      (Fin.cons 0 fun j : Fin m => j.succ.succ : Fin (m + 1) → Fin (m + 2)) := by
    intro i j hij
    refine Fin.cases (Fin.cases (fun _ => rfl) (fun j h => ?_) j)
      (fun i => Fin.cases (fun h => ?_) (fun j h => ?_) j) i hij
    · simp only [Fin.cons_zero, Fin.cons_succ] at h
      exact absurd h.symm (Fin.succ_ne_zero _)
    · simp only [Fin.cons_zero, Fin.cons_succ] at h
      exact absurd h (Fin.succ_ne_zero _)
    · simp only [Fin.cons_succ] at h
      rw [Fin.succ_injective _ (Fin.succ_injective _ h)]
  have hONB : Orthonormal ℝ (Fin.cons (b 0) b' : Fin (m + 1) → EuclideanSpace ℝ ι) := by
    rw [hcons]; exact b.orthonormal.comp _ hinj
  have hk2 : ((Fintype.card ι : ℝ) - 2) = m := by rw [hcard]; push_cast; ring
  have hkey : (fun Z : EuclideanSpace ℝ ι => regInterceptStat x fun i => c * x i + σ * Z i) =
      fun Z => ⟪b 0, Z⟫ / √((∑ j, ⟪b' j, Z⟫ ^ 2) / m) := by
    funext Z
    have hi0 : ⟪b 0, Z⟫ = (∑ i, a i * Z i) / r := by
      rw [hb0, hf1, inner_toLp_eq_sum, Finset.sum_div]
      exact Finset.sum_congr rfl fun i _ => by ring
    have hi1 : ⟪b 1, Z⟫ = (∑ i, x i * Z i) / q := by
      rw [hb1, hf2, inner_toLp_eq_sum, Finset.sum_div]
      exact Finset.sum_congr rfl fun i _ => by ring
    have hpars := b.sum_sq_inner_right Z
    rw [Fin.sum_univ_succ, Fin.sum_univ_succ, Fin.succ_zero_eq_one,
      EuclideanSpace.real_norm_sq_eq] at hpars
    have hR : regRSS x (fun i => Z i) = ∑ j, ⟪b' j, Z⟫ ^ 2 := by
      rw [regRSS_eq hS, hb']
      rw [hi0, hi1] at hpars
      rw [div_pow, div_pow, hr2, hq2] at hpars
      linarith
    have hR0 : 0 ≤ (∑ j, ⟪b' j, Z⟫ ^ 2) / m :=
      div_nonneg (Finset.sum_nonneg fun j _ => sq_nonneg _) (Nat.cast_nonneg m)
    have hint : regIntercept x (fun i => c * x i + σ * Z i) = σ * (r * ⟪b 0, Z⟫) := by
      rw [regIntercept_eq_sum, hi0, mul_div_cancel₀ _ hr0.ne', Finset.mul_sum]
      have : ∀ i, a i * (c * x i + σ * Z i) = c * (a i * x i) + σ * (a i * Z i) := fun i => by
        ring
      rw [Finset.sum_congr rfl fun i _ => this i, Finset.sum_add_distrib, ← Finset.mul_sum,
        ← Finset.mul_sum, hax, mul_zero, zero_add]
    rw [regInterceptStat, regRSS_add_smul hS, hint, hR, hk2, ← sum_regInterceptCoef_sq hS,
      ← hr2]
    rw [show (σ ^ 2 * ∑ j, ⟪b' j, Z⟫ ^ 2) / m * r ^ 2 =
        (σ * r) ^ 2 * ((∑ j, ⟪b' j, Z⟫ ^ 2) / m) by ring, Real.sqrt_mul' _ hR0,
      Real.sqrt_sq (by positivity), ← mul_assoc, mul_div_mul_left _ _ (by positivity)]
  rw [hkey]
  exact stdGaussian_map_tStat hONB

@[fun_prop]
theorem measurable_regInterceptStat (x : ι → ℝ) :
    Measurable fun z : ι → ℝ => regInterceptStat x z := by
  have h1 : Measurable fun z : ι → ℝ => regIntercept x z := by
    simp only [regIntercept_eq_sum]
    fun_prop
  have hs : Measurable fun z : ι → ℝ => regSlope x z := by
    unfold regSlope
    fun_prop
  have h2 : Measurable fun z : ι → ℝ => regRSS x z := by
    unfold regRSS
    fun_prop
  unfold regInterceptStat
  exact h1.div ((h2.div_const _).mul_const _).sqrt

end Law

/-! ### Egger's test -/

section Egger

variable {ι : Type*} [Fintype ι]

/-- The **Egger least squares objective** `∑ (yᵢ / sᵢ - α - β / sᵢ)²`: the residual sum of
squares of the standardized effects on the precisions. -/
noncomputable def eggerObj (se y : ι → ℝ) (α β : ℝ) : ℝ :=
  ∑ i, (y i / se i - α - β * (1 / se i)) ^ 2

/-- The **precision weighted objective** `∑ (yᵢ - a - b sᵢ)² / sᵢ²` of the regression of the
effect on its standard error. -/
noncomputable def eggerWeightedObj (se y : ι → ℝ) (a b : ℝ) : ℝ :=
  ∑ i, 1 / se i ^ 2 * (y i - a - b * se i) ^ 2

/-- The **Egger intercept**: the least squares intercept of the regression of `yᵢ / sᵢ` on
`1 / sᵢ` (Egger et al. 1997). -/
noncomputable def eggerIntercept (se y : ι → ℝ) : ℝ :=
  regIntercept (fun i => 1 / se i) fun i => y i / se i

/-- The **Egger test statistic**: the Egger intercept divided by its estimated standard error. -/
noncomputable def eggerStat (se y : ι → ℝ) : ℝ :=
  regInterceptStat (fun i => 1 / se i) fun i => y i / se i

/-- With two different standard errors the precisions are not all equal: `Sₓₓ ≠ 0`. -/
theorem regSxx_precision_ne_zero {se : ι → ℝ}
    (hdist : ∃ i j, se i ≠ se j) : regSxx (fun i => 1 / se i) ≠ 0 := by
  obtain ⟨i, j, hij⟩ := hdist
  intro h0
  have h := (Finset.sum_eq_zero_iff_of_nonneg fun l (_ : l ∈ Finset.univ) =>
    sq_nonneg ((fun i => 1 / se i) l - regMean fun i => 1 / se i)).1 h0
  have hi := pow_eq_zero_iff two_ne_zero |>.1 (h i (Finset.mem_univ i))
  have hj := pow_eq_zero_iff two_ne_zero |>.1 (h j (Finset.mem_univ j))
  have : 1 / se i = 1 / se j := by linarith
  exact hij (by simpa [one_div, inv_inj] using this)

/-- **The exact null law of Egger's test.** Let the estimates be independent with
`Yᵢ ~ N(θ, σ² sᵢ²)`, standard errors `sᵢ > 0` of which two differ, scale `σ² > 0`, from
`k = m + 2` studies with `m ≥ 1`. Then the Egger statistic has the exact law `tₘ = t_{k-2}`.
Proof: `yᵢ / sᵢ = θ / sᵢ + √σ² Zᵢ` with `Z = ((yᵢ - θ) / √(σ² sᵢ²))ᵢ ~ N(0, I)`, and
`map_stdGaussian_regInterceptStat`. -/
theorem hasLaw_eggerStat {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
    {Y : ι → Ω → ℝ} {θ : ℝ} {m : ℕ} (hcard : Fintype.card ι = m + 2) (hm : 1 ≤ m)
    {se : ι → ℝ} (hse : ∀ i, 0 < se i) (hdist : ∃ i j, se i ≠ se j) {σ2 : ℝ} (hσ : 0 < σ2)
    (hind : iIndepFun Y P) (hY : ∀ i, HasLaw (Y i) (gaussianReal θ (σ2 * se i ^ 2).toNNReal) P) :
    HasLaw (fun ω => eggerStat se fun i => Y i ω) (studentT m) P := by
  have hS := regSxx_precision_ne_zero hdist
  have hs : ∀ i, 0 < σ2 * se i ^ 2 := fun i => by have := hse i; positivity
  have hstd := pi_gaussianReal_map_standardize (μ := fun _ => θ) hs
  have hkey : (fun y : ι → ℝ => eggerStat se y) =
      (fun Z : EuclideanSpace ℝ ι =>
        regInterceptStat (fun i => 1 / se i) fun i => θ * (1 / se i) + √σ2 * Z i) ∘
        standardize (fun _ => θ) (fun i => σ2 * se i ^ 2) := by
    funext y
    simp only [Function.comp_apply, eggerStat]
    congr 1
    funext i
    change y i / se i = θ * (1 / se i) + √σ2 * ((y i - θ) / √(σ2 * se i ^ 2))
    have hsσ : 0 < √σ2 := Real.sqrt_pos.2 hσ
    rw [Real.sqrt_mul hσ.le, Real.sqrt_sq (hse i).le]
    have := (hse i).ne'
    field_simp
    ring
  have hlaw : HasLaw (fun y : ι → ℝ => eggerStat se y) (studentT m)
      (Measure.pi fun i => gaussianReal θ (σ2 * se i ^ 2).toNNReal) := by
    refine ⟨((measurable_regInterceptStat _).comp
      (by fun_prop : Measurable fun y : ι → ℝ => fun i => y i / se i)).aemeasurable, ?_⟩
    rw [hkey, ← Measure.map_map (by fun_prop) (measurable_standardize _ _), hstd]
    exact map_stdGaussian_regInterceptStat hcard hm hS θ (Real.sqrt_pos.2 hσ)
  exact hlaw.comp (hind.hasLaw_pi hY)

/-- **Egger's test in the Gaussian common effect model**: if the estimates form a Gaussian
common effect model with variances `sᵢ²`, two standard errors differ, and `k = m + 2`, `m ≥ 1`,
then the Egger statistic has the exact law `t_{k-2}`. -/
theorem IsGaussianCommonEffectModel.hasLaw_eggerStat {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {P : Measure Ω} {Y : ι → Ω → ℝ} {θ : ℝ} {se : ι → ℝ}
    (h : IsGaussianCommonEffectModel P Y θ fun i => se i ^ 2) (hse : ∀ i, 0 < se i)
    (hdist : ∃ i j, se i ≠ se j) {m : ℕ} (hcard : Fintype.card ι = m + 2) (hm : 1 ≤ m) :
    HasLaw (fun ω => eggerStat se fun i => Y i ω) (studentT m) P :=
  MetaAnalysis.hasLaw_eggerStat hcard hm hse hdist one_pos h.indep
    fun i => by simpa only [one_mul] using h.hasLaw i

/-- **Two forms of Egger's regression**: for `sᵢ > 0`, the Egger objective at `(α, β)` equals
the precision weighted objective at intercept `β` and slope `α`, so `(α̂, β̂)` minimizes the
first exactly when `(β̂, α̂)` minimizes the second: the Egger intercept is the slope of the
weighted regression of the effect on its standard error. Proof:
`(yᵢ / sᵢ - α - β / sᵢ)² = (yᵢ - β - α sᵢ)² / sᵢ²`. -/
theorem eggerObj_eq_weightedObj {se : ι → ℝ} (hse : ∀ i, 0 < se i) (y : ι → ℝ) :
    (∀ α β, eggerObj se y α β = eggerWeightedObj se y β α) ∧
      ∀ α β, ((∀ a b, eggerObj se y α β ≤ eggerObj se y a b) ↔
        ∀ a b, eggerWeightedObj se y β α ≤ eggerWeightedObj se y a b) := by
  have h : ∀ α β, eggerObj se y α β = eggerWeightedObj se y β α := by
    intro α β
    refine Finset.sum_congr rfl fun i _ => ?_
    have := (hse i).ne'
    field_simp
    ring
  refine ⟨h, fun α β => ⟨fun hm a b => ?_, fun hm a b => ?_⟩⟩
  · rw [← h, ← h]
    exact hm b a
  · rw [h, h]
    exact hm b a

/-- **The Egger intercept minimizes the Egger objective**: with two different standard errors,
`(α̂, β̂)` is a least squares fit of the Egger regression. -/
theorem eggerObj_le {se : ι → ℝ} [Nonempty ι] (hdist : ∃ i j, se i ≠ se j) (y : ι → ℝ) (α β : ℝ) :
    eggerObj se y (eggerIntercept se y) (regSlope (fun i => 1 / se i) fun i => y i / se i) ≤
      eggerObj se y α β := by
  have hS := regSxx_precision_ne_zero hdist
  have h := regRSS_le hS (fun i => y i / se i) α β
  exact h

/-- **Egger's regression under the common effect model, in expectation.** If the estimates form
a common effect model with variances `sᵢ²`, `sᵢ > 0`: the errors `uᵢ = yᵢ / sᵢ - θ / sᵢ` have mean
`0` and variance `1`; the expected Egger objective is `∑ ((θ - β) / sᵢ - α)² + k`; and when two
standard errors differ the expected objective has the unique minimizer `α = 0`, `β = θ`: the
population Egger intercept is `0`. -/
theorem IsCommonEffectModel.integral_eggerObj {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {P : Measure Ω} {y : ι → Ω → ℝ} {θ : ℝ} {se : ι → ℝ}
    (h : IsCommonEffectModel P y θ fun i => se i ^ 2) (hse : ∀ i, 0 < se i) :
    (∀ i, ∫ ω, (y i ω / se i - θ * (1 / se i)) ∂P = 0 ∧
        Var[fun ω => y i ω / se i - θ * (1 / se i); P] = 1) ∧
      (∀ α β, ∫ ω, eggerObj se (fun i => y i ω) α β ∂P =
        ∑ i, ((θ - β) * (1 / se i) - α) ^ 2 + Fintype.card ι) ∧
      ((∃ i j, se i ≠ se j) → ∀ α β, (α, β) ≠ (0, θ) →
        ∫ ω, eggerObj se (fun i => y i ω) 0 θ ∂P < ∫ ω, eggerObj se (fun i => y i ω) α β ∂P) := by
  have := h.isProbabilityMeasure
  have hdm : ∀ i, MemLp (fun ω => y i ω / se i) 2 P := fun i => by
    simpa only [div_eq_mul_inv] using (h.memLp i).mul_const (se i)⁻¹
  set u : ι → Ω → ℝ := fun i ω => y i ω / se i - θ * (1 / se i) with hu
  have hum : ∀ i, MemLp (u i) 2 P := fun i => (hdm i).sub (memLp_const _)
  have hu0 : ∀ i, ∫ ω, u i ω ∂P = 0 := by
    intro i
    simp only [hu]
    rw [integral_sub ((hdm i).integrable one_le_two) (integrable_const _),
      integral_div, h.integral_eq, integral_const, smul_eq_mul, probReal_univ, one_mul]
    have := (hse i).ne'
    field_simp
    ring
  have hu1 : ∀ i, Var[u i; P] = 1 := by
    intro i
    simp only [hu]
    rw [variance_sub_const (hdm i).aestronglyMeasurable]
    have : (fun ω => y i ω / se i) = fun ω => (1 / se i) * y i ω := by
      funext ω; ring
    rw [this, variance_const_mul, h.variance_eq]
    have := (hse i).ne'
    field_simp
  have hsq : ∀ i c, ∫ ω, (u i ω + c) ^ 2 ∂P = 1 + c ^ 2 := by
    intro i c
    have hint2 := (hum i).integrable_sq
    have hint1 := (hum i).integrable one_le_two
    have : (fun ω => (u i ω + c) ^ 2) = fun ω => u i ω ^ 2 + (2 * c * u i ω + c ^ 2) := by
      funext ω; ring
    rw [this, integral_add (f := fun ω => u i ω ^ 2) (g := fun ω => 2 * c * u i ω + c ^ 2) hint2
      ((hint1.const_mul _).add (integrable_const _)),
      integral_add (f := fun ω => 2 * c * u i ω) (g := fun _ => c ^ 2) (hint1.const_mul _)
        (integrable_const _), integral_const_mul, hu0,
      ← variance_of_integral_eq_zero (hum i).aemeasurable (hu0 i), hu1, integral_const,
      smul_eq_mul, probReal_univ, one_mul]
    ring
  have hobj : ∀ α β ω, eggerObj se (fun i => y i ω) α β =
      ∑ i, (u i ω + ((θ - β) * (1 / se i) - α)) ^ 2 := by
    intro α β ω
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [hu]
    ring
  have hE : ∀ α β, ∫ ω, eggerObj se (fun i => y i ω) α β ∂P =
      ∑ i, ((θ - β) * (1 / se i) - α) ^ 2 + Fintype.card ι := by
    intro α β
    simp only [hobj]
    rw [integral_finsetSum (f := fun i ω => (u i ω + ((θ - β) * (1 / se i) - α)) ^ 2) _
      fun i _ => ((hum i).add (memLp_const _)).integrable_sq]
    simp only [hsq, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
      mul_one]
    ring
  refine ⟨fun i => ⟨hu0 i, hu1 i⟩, hE, fun ⟨i, j, hij⟩ α β hne => ?_⟩
  rw [hE, hE]
  have h0 : ∑ l, ((θ - θ) * (1 / se l) - 0) ^ 2 = 0 := by simp
  rw [h0, zero_add]
  have hnn : 0 ≤ ∑ l, ((θ - β) * (1 / se l) - α) ^ 2 :=
    Finset.sum_nonneg fun l _ => sq_nonneg _
  rcases hnn.lt_or_eq with hlt | heq
  · linarith
  · exfalso
    have h0 := (Finset.sum_eq_zero_iff_of_nonneg fun l _ => sq_nonneg
      ((θ - β) * (1 / se l) - α)).1 heq.symm
    have hi := pow_eq_zero_iff (n := 2) two_ne_zero |>.1 (h0 i (Finset.mem_univ i))
    have hj := pow_eq_zero_iff (n := 2) two_ne_zero |>.1 (h0 j (Finset.mem_univ j))
    have hsub : (θ - β) * (1 / se i - 1 / se j) = 0 := by linear_combination hi - hj
    have hpij : 1 / se i - 1 / se j ≠ 0 := by
      rw [sub_ne_zero]
      intro hc
      exact hij (by simpa using hc)
    have hβ : θ - β = 0 := (mul_eq_zero.1 hsub).resolve_right hpij
    have hα : α = 0 := by rw [hβ, zero_mul] at hi; linarith
    exact hne (by rw [hα, show β = θ by linarith])

end Egger

end MetaAnalysis

end CausalInference
