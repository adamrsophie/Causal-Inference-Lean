/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.MetaAnalysis.HierarchicalPosterior
public import CausalInference.Bias.HazardMixtureGeneral
public import Mathlib.Probability.Distributions.Poisson.Basic

/-!
# Gamma and Poisson conjugacy

Let `y₁, …, yₙ` be i.i.d. Poisson with rate `λ` given `λ`, and let the prior be
`λ ~ Gamma(a, b)` (shape `a > 0`, rate `b > 0`, Mathlib's `gammaMeasure a b`). With
`S = ∑ yᵢ`:

* **Kernel identity** (`gammaPDFReal_mul_exp_mul_pow`): the gamma density times
  `exp(-m x) x^S` is a constant times the `Gamma(a + S, b + m)` density, for every `x ≠ 0`.
* **Conjugacy** (`gammaPoisson_posterior`), in the form of `BiasAnalysis.Bayesian`
  (`betaBinomial_posterior`): the marginal likelihood is
  `Z = b^a Γ(a + S) / (Γ(a) (b + n)^(a + S) ∏ yᵢ!)`, positive and finite, and the normalized
  posterior is `Gamma(a + S, b + n)`.
* **Posterior mean** (`gammaPoisson_posteriorMean`): `(a + S)/(b + n)`, the shrinkage
  `B (a/b) + (1 - B) ȳ` of the sample mean toward the prior mean with `B = b/(b + n)`.
* **Predictive law** (`gammaPoisson_predictive`): under `Gamma(α, β)` the probability that a new
  Poisson count equals `k` is the negative binomial probability
  `Γ(α + k) / (Γ(α) k!) (β/(β + 1))^α (1/(β + 1))^k`; with the posterior parameters this is the
  posterior predictive law.

The likelihood `poissonLikelihood` is the product of the Poisson probabilities of Mathlib's
`poissonMeasure` (`poissonLikelihood_eq`).

## Main definitions

* `poissonLikelihood`.

## Main results

* `gammaPDFReal_mul_exp_mul_pow`, `poissonLikelihood_eq`, `gammaPoisson_posterior`,
  `gammaPoisson_posteriorMean`, `gammaPoisson_predictive`.

## References

* A. Gelman, J. B. Carlin, H. S. Stern, D. B. Dunson, A. Vehtari and D. B. Rubin, *Bayesian Data
  Analysis*, third edition (2013).
-/

@[expose] public section

namespace CausalInference

namespace MetaAnalysis

open MeasureTheory ProbabilityTheory Finset Set
open scoped ENNReal NNReal Nat

/-- The **gamma kernel identity**: for `x ≠ 0`, `a, b > 0`, `m ≥ 0` and `S ∈ ℕ`,
`γ(x; a, b) exp(-m x) x^S = b^a Γ(a + S) / (Γ(a) (b + m)^(a + S)) · γ(x; a + S, b + m)`. -/
theorem gammaPDFReal_mul_exp_mul_pow {a b m : ℝ} (ha : 0 < a) (hb : 0 < b) (hm : 0 ≤ m)
    (S : ℕ) {x : ℝ} (hx : x ≠ 0) :
    gammaPDFReal a b x * (Real.exp (-(m * x)) * x ^ S) =
      b ^ a * Real.Gamma (a + S) / (Real.Gamma a * (b + m) ^ (a + S)) *
        gammaPDFReal (a + S) (b + m) x := by
  have hbm : 0 < b + m := by linarith
  have hG := Real.Gamma_pos_of_pos ha
  have hG' := Real.Gamma_pos_of_pos (show 0 < a + S by positivity)
  rcases hx.lt_or_gt with hneg | hpos
  · simp [gammaPDFReal, not_le.2 hneg]
  · simp only [gammaPDFReal, hpos.le, ↓reduceIte]
    rw [show a + S - 1 = (a - 1) + S by ring, Real.rpow_add_natCast hpos.ne',
      show -((b + m) * x) = -(b * x) + -(m * x) by ring, Real.exp_add]
    have : 0 < (b + m) ^ (a + S) := Real.rpow_pos_of_pos hbm _
    field_simp

/-- The **Poisson likelihood** `λ ↦ ∏ᵢ e^{-λ} λ^{yᵢ} / yᵢ!` of counts `y`. -/
noncomputable def poissonLikelihood {ι : Type*} [Fintype ι] (y : ι → ℕ) (lam : ℝ) : ℝ :=
  ∏ i, Real.exp (-lam) * lam ^ y i / (y i)!

variable {ι : Type*} [Fintype ι]

/-- For `λ ≥ 0` the likelihood is the product of the probabilities of Mathlib's Poisson law. -/
theorem poissonLikelihood_eq (y : ι → ℕ) {lam : ℝ} (hlam : 0 ≤ lam) :
    poissonLikelihood y lam = ∏ i, (poissonMeasure lam.toNNReal).real {y i} := by
  simp only [poissonLikelihood, poissonMeasure_real_singleton, Real.coe_toNNReal _ hlam]

theorem poissonLikelihood_nonneg (y : ι → ℕ) {lam : ℝ} (hlam : 0 ≤ lam) :
    0 ≤ poissonLikelihood y lam :=
  Finset.prod_nonneg fun i _ => by positivity

/-- The likelihood is `e^{-nλ} λ^S / ∏ yᵢ!`. -/
theorem poissonLikelihood_eq_exp (y : ι → ℕ) (lam : ℝ) :
    poissonLikelihood y lam =
      Real.exp (-(Fintype.card ι * lam)) * lam ^ (∑ i, y i) / ∏ i, ((y i)! : ℝ) := by
  rw [poissonLikelihood, Finset.prod_div_distrib, Finset.prod_mul_distrib, Finset.prod_const,
    Finset.prod_pow_eq_pow_sum, Finset.card_univ, ← Real.exp_nat_mul, mul_neg]

/-- The marginal likelihood `b^a Γ(a + S) / (Γ(a) (b + n)^(a + S) ∏ yᵢ!)` of the gamma and
Poisson model. -/
noncomputable def gammaPoissonEvidence (a b : ℝ) (y : ι → ℕ) : ℝ :=
  b ^ a * Real.Gamma (a + ∑ i, y i) /
    (Real.Gamma a * (b + Fintype.card ι) ^ (a + ∑ i, y i)) / ∏ i, ((y i)! : ℝ)

theorem gammaPoissonEvidence_pos {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (y : ι → ℕ) :
    0 < gammaPoissonEvidence a b y := by
  have hG := Real.Gamma_pos_of_pos ha
  have hG' := Real.Gamma_pos_of_pos (show 0 < a + ∑ i, (y i : ℝ) by positivity)
  have hF : (0 : ℝ) < ∏ i, ((y i)! : ℝ) := Finset.prod_pos fun i _ => by positivity
  have : 0 < (b + Fintype.card ι) ^ (a + ∑ i, (y i : ℝ)) := Real.rpow_pos_of_pos (by positivity) _
  unfold gammaPoissonEvidence
  push_cast
  positivity

/-- **Gamma and Poisson conjugacy.** For counts `y₁, …, yₙ` and the prior `Gamma(a, b)`,
`a, b > 0`: the marginal likelihood `∫ L dΠ` is `gammaPoissonEvidence a b y`, positive and finite,
and the normalized posterior is `Gamma(a + ∑ yᵢ, b + n)`. -/
theorem gammaPoisson_posterior {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (y : ι → ℕ) :
    ∫⁻ lam, ENNReal.ofReal (poissonLikelihood y lam) ∂gammaMeasure a b =
        ENNReal.ofReal (gammaPoissonEvidence a b y) ∧
      normalizedPosterior (gammaMeasure a b) (fun lam => ENNReal.ofReal (poissonLikelihood y lam)) =
        gammaMeasure (a + ∑ i, (y i : ℝ)) (b + Fintype.card ι) := by
  have hS : ∑ i, (y i : ℝ) = ((∑ i, y i : ℕ) : ℝ) := by push_cast; rfl
  have hF : (0 : ℝ) < ∏ i, ((y i)! : ℝ) := Finset.prod_pos fun i _ => by positivity
  have hn : (0 : ℝ) ≤ Fintype.card ι := Nat.cast_nonneg _
  have hL : Measurable fun lam => ENNReal.ofReal (poissonLikelihood y lam) := by
    unfold poissonLikelihood
    fun_prop
  have hne : ∀ᵐ x ∂(volume : Measure ℝ), x ≠ 0 := compl_mem_ae_iff.2 (measure_singleton 0)
  have key := normalizedPosterior_eq_of_mul_eq (κ := volume) (f := gammaPDF a b)
    (Bias.HazardMixtureGeneral.measurable_gammaPDF' a b) hL
    (c := ENNReal.ofReal (gammaPoissonEvidence a b y))
    (ENNReal.ofReal_pos.2 (gammaPoissonEvidence_pos ha hb y)).ne' ENNReal.ofReal_ne_top
    (g := gammaPDF (a + ∑ i, (y i : ℝ)) (b + Fintype.card ι)) ?_
    (lintegral_gammaPDF_eq_one (by rw [hS]; positivity) (by positivity))
  · exact key
  filter_upwards [hne] with x hx
  have hpdf : 0 ≤ gammaPDFReal a b x := gammaPDFReal_nonneg ha hb x
  rw [gammaPDF, gammaPDF, ← ENNReal.ofReal_mul hpdf,
    ← ENNReal.ofReal_mul (gammaPoissonEvidence_pos ha hb y).le, poissonLikelihood_eq_exp]
  congr 1
  have h := gammaPDFReal_mul_exp_mul_pow ha hb hn (∑ i, y i) hx
  rw [hS, gammaPoissonEvidence]
  rw [show gammaPDFReal a b x * (Real.exp (-(Fintype.card ι * x)) * x ^ (∑ i, y i) /
      ∏ i, ((y i)! : ℝ)) = gammaPDFReal a b x * (Real.exp (-(Fintype.card ι * x)) *
      x ^ (∑ i, y i)) / ∏ i, ((y i)! : ℝ) by ring, h]
  field_simp

/-- The mean of `Gamma(α, β)` is `α / β`. -/
theorem integral_id_gammaMeasure {α β : ℝ} (hα : 0 < α) (hβ : 0 < β) :
    ∫ x, x ∂gammaMeasure α β = α / β := by
  have h := Bias.HazardMixtureGeneral.integral_mul_exp_neg_gammaMeasure hα hβ (le_refl 0)
  simp only [mul_zero, neg_zero, Real.exp_zero, mul_one, add_zero, div_self hβ.ne',
    Real.one_rpow] at h
  exact h

/-- **The posterior mean shrinks the sample mean toward the prior mean**: for `n ≥ 1` counts the
mean of the posterior `Gamma(a + S, b + n)` is `(a + S)/(b + n) = B (a/b) + (1 - B) ȳ` with
`B = b/(b + n) ∈ (0, 1)` and `ȳ = S / n`. -/
theorem gammaPoisson_posteriorMean [Nonempty ι] {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (y : ι → ℕ) :
    ∫ lam, lam ∂gammaMeasure (a + ∑ i, (y i : ℝ)) (b + Fintype.card ι) =
        (a + ∑ i, (y i : ℝ)) / (b + Fintype.card ι) ∧
      (a + ∑ i, (y i : ℝ)) / (b + Fintype.card ι) =
        b / (b + Fintype.card ι) * (a / b) +
          (1 - b / (b + Fintype.card ι)) * ((∑ i, (y i : ℝ)) / Fintype.card ι) ∧
      b / (b + Fintype.card ι) ∈ Set.Ioo 0 1 := by
  have hn : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
  refine ⟨integral_id_gammaMeasure (by positivity) (by positivity), ?_, ?_⟩
  · field_simp
    ring
  · exact ⟨by positivity, (div_lt_one (by positivity)).2 (by linarith)⟩

/-- **The negative binomial predictive law**: under the gamma law `Gamma(α, β)`, `α, β > 0`, the
probability that a Poisson count with rate `λ` equals `k`, `∫ e^{-λ} λ^k / k! dΓ(λ)`, is
`Γ(α + k) / (Γ(α) k!) · (β / (β + 1))^α · (1 / (β + 1))^k`. With `α = a + S` and `β = b + n` it is
the posterior predictive probability of a new count in the gamma and Poisson model. -/
theorem gammaPoisson_predictive {α β : ℝ} (hα : 0 < α) (hβ : 0 < β) (k : ℕ) :
    ∫ lam, Real.exp (-lam) * lam ^ k / (k.factorial : ℝ) ∂gammaMeasure α β =
      Real.Gamma (α + k) / (Real.Gamma α * (k.factorial : ℝ)) * (β / (β + 1)) ^ α *
        (1 / (β + 1)) ^ k := by
  have hβ1 : 0 < β + 1 := by linarith
  rw [Bias.HazardMixtureGeneral.integral_gammaMeasure hα hβ]
  have e : ∀ x ∈ Ioi (0 : ℝ), β ^ α / Real.Gamma α * x ^ (α - 1) * Real.exp (-(β * x)) *
      (Real.exp (-x) * x ^ k / (k.factorial : ℝ)) =
      β ^ α / (Real.Gamma α * (k.factorial : ℝ)) *
        (x ^ (α + k - 1) * Real.exp (-((β + 1) * x))) := by
    intro x hx
    have hx0 : x ≠ 0 := (show 0 < x from hx).ne'
    rw [show α + k - 1 = (α - 1) + k by ring, Real.rpow_add_natCast hx0,
      show -((β + 1) * x) = -(β * x) + -x by ring, Real.exp_add]
    have := Real.Gamma_pos_of_pos hα
    field_simp
  rw [setIntegral_congr_fun measurableSet_Ioi e, integral_const_mul,
    Real.integral_rpow_mul_exp_neg_mul_Ioi (by positivity) hβ1]
  have hG := (Real.Gamma_pos_of_pos hα).ne'
  rw [Real.rpow_add (by positivity), Real.rpow_natCast,
    show (β / (β + 1)) ^ α = β ^ α * (1 / (β + 1)) ^ α by
      rw [← Real.mul_rpow hβ.le (by positivity), mul_one_div]]
  field_simp

end MetaAnalysis

end CausalInference
