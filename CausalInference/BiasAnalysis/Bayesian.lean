/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.Bias.Misclassification
public import Mathlib.Probability.Distributions.Beta
public import Mathlib.Probability.Distributions.Binomial
public import Mathlib.Algebra.Polynomial.Coeff

/-!
# Bayesian bias analysis

The probability facts behind Bayesian and probabilistic bias analysis for misclassification.
Source: Matthew P. Fox, Richard F. MacLehose and Timothy L. Lash (2021), *Applying Quantitative
Bias Analysis to Epidemiologic Data*, second edition: Chapter 11 ("Bias Analysis Using Bayesian
Methods") including its appendix, the appendix of Chapter 8 ("Sampling Models for Exposure
Misclassification") and Chapter 9 (record level reclassification, Tables 9.5 to 9.8).

## Main results

* Metropolis algorithm (Equation 11.9), finite state version: `metropolisKernel` with the
  rejected mass on the diagonal; `metropolisKernel_sum` (rows sum to one, an identity),
  `metropolisKernel_nonneg` (entrywise nonnegative for a nonnegative target and a stochastic
  proposal), `metropolis_detailedBalance` and `metropolis_stationary` (a nonnegative target is
  invariant for a symmetric proposal), `metropolis_invariant_probability` (with a symmetric
  stochastic proposal the kernel is a stochastic matrix and the normalized target is an invariant
  probability vector), `acceptance_const_mul` (the normalizing integral of Equation 11.7
  cancels), and `metropolis_asymmetric_counterexample` (with a stochastic but asymmetric proposal
  the target need not be invariant). The book's random walk proposal on `[0, 1]` is continuous;
  only the finite state version is proved.
* Likelihood through the apparent prevalence (Equations 11.3 and 11.4): `misclassLikelihood`,
  `misclassLikelihood_eq`, `misclassLikelihood_congr`, `caseControl_likelihood_congr` (the
  two-group likelihood of Equations 11.10 to 11.13), and the non-identification results
  `exists_classification_of_observedPrevalence` and `exists_same_misclassLikelihood`: every true
  prevalence is compatible, through some better than chance classification, with every apparent
  prevalence in `(0, 1)`; `caseControl_not_identified` and its numerical instance
  `caseControl_not_identified_example`: with one classification shared by cases and controls
  (Equation 11.13) the prevalences, and the odds ratio, are not identified either. Builds on
  `Bias.observedPrevalence` and strengthens `Bias.prevalence_not_identified`.
* Beta and binomial conjugacy (the beta prior of Equation 11.5, binomial likelihood of Equation
  11.2, Bayes' theorem of Equation 11.7): `betaPDFReal_mul_binomPMF`,
  `betaMeasure_withDensity_binomPMF`, `betaBinomial_posterior`.
* Gibbs full conditionals of the Chapter 11 appendix (Tables 11.7 and 11.8): the kernel
  identities `gibbsJoint_se`, `gibbsJoint_sp`, `gibbsJoint_prevalence` (beta conditionals),
  `gibbsJoint_W` and `gibbsJoint_Z` (binomial conditionals with the predictive values),
  `binomPMF_one_sub` (sampling `Y` or `Z` agrees), `nondifferential_se` and `nondifferential_sp`
  (pooled counts); and their normalized forms, with positive prior shapes and conditioning values
  in `(0, 1)`: `gibbs_se_conditional`, `gibbs_sp_conditional`, `gibbs_prevalence_conditional`,
  `nondifferential_se_conditional`, `nondifferential_sp_conditional` (positive normalizer, and the
  normalized slice is the beta law) and `gibbs_WZ_conditional` (the blocked update of the latent
  cells on fixed margins is `Bin(a, ppv) ⊗ Bin(b, npv)`).
* Binomial thinning (Chapter 8 appendix): `binomial_thinning` and its form for Mathlib's
  binomial law `binomial_thinning_binomial`.
* Record level versus summary level reclassification (Chapter 9): `integral_reclassified_count`
  and `integral_reclassified_binomial`.
* `Examples`: the depression screening example of Chapter 11, Tables 9.7 and 9.8, and the first
  Gibbs iteration of the Chapter 11 appendix.

The thinning and Gibbs results are stated for mass functions and densities (the joint law
written as a function of the parameters and latent counts, and its slices as measures on `ℝ` or
as normalized mass functions); they are not stated for random variables or for a multinomial
measure.

`binomPMF` is the binomial mass function `C(n, k) p^k (1 - p)^(n - k)`; `binomPMF_eq_binomial`
identifies it with Mathlib's `ProbabilityTheory.binomial`. The kernel identity
`betaPDFReal_mul_pow` is the common step of all conjugate updates.
-/

@[expose] public section

namespace CausalInference

namespace BiasAnalysis

namespace Bayesian

open Finset

section Metropolis

variable {S : Type*}

/-- The Metropolis acceptance probability `min(1, w y / w x)` for a move from `x` to `y` under a
target weight `w` (Fox, MacLehose and Lash 2021, Equation 11.9). -/
noncomputable def acceptance (w : S → ℝ) (x y : S) : ℝ := min 1 (w y / w x)

/-- The Metropolis transition kernel with proposal `q`: a move from `x` to `y ≠ x` has probability
`q x y` times the acceptance probability, and the rejected mass stays at `x`. -/
noncomputable def metropolisKernel [Fintype S] [DecidableEq S] (w : S → ℝ) (q : S → S → ℝ)
    (x y : S) : ℝ :=
  if x = y then 1 - ∑ z ∈ univ.erase x, q x z * acceptance w x z
  else q x y * acceptance w x y

/-- Each row of the Metropolis kernel sums to one. This is an identity for every `w` and `q`;
the entries are nonnegative only under the hypotheses of `metropolisKernel_nonneg`. -/
theorem metropolisKernel_sum [Fintype S] [DecidableEq S] (w : S → ℝ) (q : S → S → ℝ) (x : S) :
    ∑ y, metropolisKernel w q x y = 1 := by
  rw [← Finset.add_sum_erase _ _ (mem_univ x)]
  have h : ∀ y ∈ univ.erase x, metropolisKernel w q x y = q x y * acceptance w x y :=
    fun y hy => by simp [metropolisKernel, Ne.symm (ne_of_mem_erase hy)]
  rw [Finset.sum_congr rfl h]
  simp [metropolisKernel]

/-- The acceptance probability lies in `[0, 1]` for a nonnegative target. -/
theorem acceptance_mem_Icc {w : S → ℝ} (hw : ∀ x, 0 ≤ w x) (x y : S) :
    acceptance w x y ∈ Set.Icc (0 : ℝ) 1 :=
  ⟨le_min zero_le_one (div_nonneg (hw y) (hw x)), min_le_left _ _⟩

/-- **The Metropolis kernel is entrywise nonnegative** for a nonnegative target and a stochastic
proposal (nonnegative entries, rows summing to one): the off-diagonal entries are products of
probabilities, and the rejected mass on the diagonal is at least
`1 - ∑_{z ≠ x} q x z ≥ q x x ≥ 0`. From a state with `w x = 0` every acceptance probability is
`min 1 (w y / 0) = 0` by the division convention, so that row of the kernel is the identity row. -/
theorem metropolisKernel_nonneg [Fintype S] [DecidableEq S] {w : S → ℝ} (hw : ∀ x, 0 ≤ w x)
    {q : S → S → ℝ} (hq0 : ∀ x y, 0 ≤ q x y) (hq1 : ∀ x, ∑ y, q x y = 1) (x y : S) :
    0 ≤ metropolisKernel w q x y := by
  unfold metropolisKernel
  split_ifs with hxy
  · have hle : ∑ z ∈ univ.erase x, q x z * acceptance w x z ≤ ∑ z ∈ univ.erase x, q x z :=
      sum_le_sum fun z _ => mul_le_of_le_one_right (hq0 x z) (acceptance_mem_Icc hw x z).2
    have hsum := hq1 x
    rw [← Finset.add_sum_erase _ _ (mem_univ x)] at hsum
    linarith [hq0 x x]
  · exact mul_nonneg (hq0 x y) (acceptance_mem_Icc hw x y).1

/-- The acceptance step depends on the target only through ratios: multiplying the target by a
nonzero constant (for instance dividing an unnormalized posterior `likelihood × prior` by the
intractable normalizing integral of Equation 11.7) leaves it unchanged. -/
theorem acceptance_const_mul (w : S → ℝ) {c : ℝ} (hc : c ≠ 0) (x y : S) :
    acceptance (fun z => c * w z) x y = acceptance w x y := by
  simp only [acceptance, mul_div_mul_left _ _ hc]

/-- Detailed balance of the Metropolis kernel: for a nonnegative target `w` and a symmetric
proposal `q`, `w x K(x, y) = w y K(y, x)`. At a state with `w x = 0` the acceptance
probability of every move into it is `min 1 (0 / w y) = 0` and both sides vanish. The identity
needs neither nonnegativity of `q` nor unit row sums. -/
theorem metropolis_detailedBalance [Fintype S] [DecidableEq S] (w : S → ℝ) (hw : ∀ x, 0 ≤ w x)
    (q : S → S → ℝ) (hq : ∀ x y, q x y = q y x) (x y : S) :
    w x * metropolisKernel w q x y = w y * metropolisKernel w q y x := by
  by_cases hxy : x = y
  · subst hxy; rfl
  simp only [metropolisKernel, hxy, Ne.symm hxy, ↓reduceIte, acceptance, hq y x]
  have key : ∀ a b : ℝ, 0 ≤ a → 0 ≤ b → a * min 1 (b / a) = min a b := by
    intro a b ha hb
    rcases ha.eq_or_lt with ha0 | ha0
    · subst ha0; simp [min_eq_left hb]
    · rw [mul_min_of_nonneg _ _ ha0.le, mul_one, mul_div_cancel₀ _ ha0.ne']
  rw [mul_left_comm, key _ _ (hw x) (hw y), mul_left_comm, key _ _ (hw y) (hw x), min_comm]

/-- Stationarity: a nonnegative target `w` is invariant for the Metropolis kernel with a
symmetric proposal, `∑ x w x K(x, y) = w y`. As an identity it needs no hypothesis on `q` beyond
symmetry; `metropolis_invariant_probability` gives the probabilistic reading. -/
theorem metropolis_stationary [Fintype S] [DecidableEq S] (w : S → ℝ) (hw : ∀ x, 0 ≤ w x)
    (q : S → S → ℝ) (hq : ∀ x y, q x y = q y x) (y : S) :
    ∑ x, w x * metropolisKernel w q x y = w y := by
  simp_rw [metropolis_detailedBalance w hw q hq _ y, ← mul_sum, metropolisKernel_sum, mul_one]

/-- **The Metropolis kernel is a stochastic matrix with the normalized target as invariant
law.** For a nonnegative target `w` with positive total mass and a symmetric stochastic proposal
`q`, the kernel has nonnegative entries and unit row sums, the normalized target
`π x = w x / ∑ z, w z` is a probability vector, and `∑ x π x K(x, y) = π y`. The kernel is the
same for `w` and `π` (`acceptance_const_mul`). -/
theorem metropolis_invariant_probability [Fintype S] [DecidableEq S] {w : S → ℝ}
    (hw : ∀ x, 0 ≤ w x) (hw1 : 0 < ∑ z, w z) {q : S → S → ℝ} (hq0 : ∀ x y, 0 ≤ q x y)
    (hq1 : ∀ x, ∑ y, q x y = 1) (hq : ∀ x y, q x y = q y x) :
    let π : S → ℝ := fun x => w x / ∑ z, w z
    (∀ x y, 0 ≤ metropolisKernel π q x y) ∧ (∀ x, ∑ y, metropolisKernel π q x y = 1) ∧
      (∀ x, 0 ≤ π x) ∧ ∑ x, π x = 1 ∧
      metropolisKernel π q = metropolisKernel w q ∧
      ∀ y, ∑ x, π x * metropolisKernel π q x y = π y := by
  intro π
  have hπ : ∀ x, 0 ≤ π x := fun x => div_nonneg (hw x) hw1.le
  have hK : metropolisKernel π q = metropolisKernel w q := by
    have hacc : acceptance π = acceptance w := by
      funext x y
      have := acceptance_const_mul w (inv_ne_zero hw1.ne') x y
      simpa only [π, div_eq_inv_mul] using this
    funext x y
    simp only [metropolisKernel, hacc]
  refine ⟨metropolisKernel_nonneg hπ hq0 hq1, metropolisKernel_sum π q, hπ, ?_, hK,
    metropolis_stationary π hπ q hq⟩
  simp only [π, ← sum_div]
  exact div_self hw1.ne'

/-- The symmetry of the proposal cannot be dropped. On two states take the uniform target
`w = 1/2` (a probability vector) and the stochastic proposal `q(true, true) = q(true, false) =
1/2`, `q(false, false) = 1`, `q(false, true) = 0`. Every other hypothesis of
`metropolis_invariant_probability` holds, yet `∑ x w x K(x, false) = 3/4 ≠ 1/2`: the target is not
invariant, and detailed balance fails. -/
theorem metropolis_asymmetric_counterexample :
    let w : Bool → ℝ := fun _ => 1 / 2
    let q : Bool → Bool → ℝ := fun x y => if x then 1 / 2 else (if y then 0 else 1)
    (∀ x, 0 ≤ w x) ∧ ∑ x, w x = 1 ∧ (∀ x y, 0 ≤ q x y) ∧ (∀ x, ∑ y, q x y = 1) ∧
      q true false ≠ q false true ∧
      ∑ x, w x * metropolisKernel w q x false = 3 / 4 ∧
      w true * metropolisKernel w q true false ≠ w false * metropolisKernel w q false true := by
  intro w q
  refine ⟨fun _ => by norm_num [w], by norm_num [w], fun x y => ?_, fun x => ?_, by norm_num [q],
    ?_, ?_⟩
  · cases x <;> cases y <;> norm_num [q]
  · cases x <;> norm_num [q]
  · simp only [metropolisKernel, acceptance, Fintype.sum_bool]
    norm_num [Finset.sum_erase_eq_sub, Fintype.sum_bool, w, q]
  · simp only [metropolisKernel, acceptance]
    norm_num [w, q]

end Metropolis

section Binomial

open Polynomial

/-- The binomial probability `C(n, k) p^k (1 - p)^(n - k)` of `k` successes in `n` trials with
success probability `p` (Fox, MacLehose and Lash 2021, Chapter 7, "Bernoulli and Binomial
Distributions"). It is zero for `k > n`. -/
def binomPMF (n : ℕ) (p : ℝ) (k : ℕ) : ℝ := n.choose k * p ^ k * (1 - p) ^ (n - k)

/-- `binomPMF` is the mass function of Mathlib's binomial law `Bin(n, p)`. -/
theorem binomPMF_eq_binomial (n k : ℕ) (p : unitInterval) :
    binomPMF n p k = (ProbabilityTheory.binomial n p).real {k} := by
  rw [ProbabilityTheory.binomial_real_singleton, binomPMF]

/-- The probability generating polynomial `(p X + (1 - p))^n` of the binomial law. -/
noncomputable def binomPoly (n : ℕ) (p : ℝ) : ℝ[X] := (C p * X + C (1 - p)) ^ n

/-- The coefficients of the generating polynomial are the binomial probabilities. -/
theorem coeff_binomPoly (n : ℕ) (p : ℝ) (k : ℕ) : (binomPoly n p).coeff k = binomPMF n p k := by
  rw [binomPoly, add_pow, finsetSum_coeff]
  have h : ∀ m ∈ range (n + 1), ((C p * X) ^ m * C (1 - p) ^ (n - m) * (n.choose m : ℝ[X])).coeff k
      = if k = m then binomPMF n p m else 0 := by
    intro m _
    have : (C p * X) ^ m * C (1 - p) ^ (n - m) * (n.choose m : ℝ[X])
        = C (binomPMF n p m) * X ^ m := by
      simp only [binomPMF, mul_pow, ← C_pow, ← Polynomial.C_eq_natCast, C_mul]
      ring
    rw [this, coeff_C_mul_X_pow]
  rw [sum_congr rfl h, sum_ite_eq]
  split_ifs with hk
  · rfl
  · simp only [mem_range, not_lt] at hk
    simp [binomPMF, Nat.choose_eq_zero_of_lt (by omega : n < k)]

/-- Binomial thinning, the equivalence of the two sampling models for exposure misclassification
(Fox, MacLehose and Lash 2021, Chapter 8, "Appendix: Sampling Models for Exposure
Misclassification"). If the true number exposed is `A ~ Bin(N, π)`, and given `A` the correctly
classified exposed `W ~ Bin(A, se)` and the falsely classified unexposed `X ~ Bin(N - A, 1 - sp)`
are drawn independently, then the observed count `a = W + X` has law `Bin(N, p)` with
`p = π se + (1 - π)(1 - sp)`, the observed prevalence. The left side is the mass of `{W + X = a}`
in the latent model, summed over `A` and over the decompositions `a = w + x`. The identity is
polynomial, so it needs no range hypotheses on `π`, `se`, `sp`. -/
theorem binomial_thinning (N : ℕ) (π se sp : ℝ) (a : ℕ) :
    ∑ A ∈ range (N + 1), binomPMF N π A *
        ∑ wx ∈ antidiagonal a, binomPMF A se wx.1 * binomPMF (N - A) (1 - sp) wx.2 =
      binomPMF N (Bias.observedPrevalence se sp π) a := by
  have hinner : ∀ A, ∑ wx ∈ antidiagonal a, binomPMF A se wx.1 * binomPMF (N - A) (1 - sp) wx.2
      = (binomPoly A se * binomPoly (N - A) (1 - sp)).coeff a := by
    intro A
    simp only [coeff_mul, coeff_binomPoly]
  have hp : C (Bias.observedPrevalence se sp π) * X + C (1 - Bias.observedPrevalence se sp π)
      = C π * (C se * X + C (1 - se)) + C (1 - π) * (C (1 - sp) * X + C (1 - (1 - sp))) := by
    rw [Bias.observedPrevalence_eq]
    simp only [map_add, map_sub, map_mul, map_one]
    ring
  have hpoly : ∑ A ∈ range (N + 1),
      C (binomPMF N π A) * (binomPoly A se * binomPoly (N - A) (1 - sp)) =
        binomPoly N (Bias.observedPrevalence se sp π) := by
    rw [binomPoly, hp, add_pow]
    refine sum_congr rfl fun m _ => ?_
    rw [mul_pow, mul_pow]
    simp only [binomPoly, binomPMF, map_mul, map_pow, map_natCast, sub_sub_cancel]
    ring
  simp_rw [hinner]
  rw [← coeff_binomPoly, ← hpoly, finsetSum_coeff]
  simp only [coeff_C_mul]

/-- The observed prevalence `π se + (1 - π)(1 - sp)` lies in the unit interval when `π`, `se`
and `sp` do. -/
theorem observedPrevalence_mem_unitInterval {se sp π : ℝ} (hse : se ∈ Set.Icc (0 : ℝ) 1)
    (hsp : sp ∈ Set.Icc (0 : ℝ) 1) (hπ : π ∈ Set.Icc (0 : ℝ) 1) :
    Bias.observedPrevalence se sp π ∈ Set.Icc (0 : ℝ) 1 := by
  obtain ⟨h1, h2⟩ := hse
  obtain ⟨h3, h4⟩ := hsp
  obtain ⟨h5, h6⟩ := hπ
  rw [Bias.observedPrevalence_eq]
  constructor <;> nlinarith [mul_nonneg h5 h1, mul_nonneg (sub_nonneg.2 h6) (sub_nonneg.2 h4)]

/-- Binomial thinning in terms of Mathlib's binomial law: with `π`, `se`, `sp` in the unit
interval, the mass of `{W + X = a}` in the latent model is `Bin(N, p) {a}` with
`p = π se + (1 - π)(1 - sp)`. -/
theorem binomial_thinning_binomial (N : ℕ) {π se sp : ℝ} (hse : se ∈ Set.Icc (0 : ℝ) 1)
    (hsp : sp ∈ Set.Icc (0 : ℝ) 1) (hπ : π ∈ Set.Icc (0 : ℝ) 1) (a : ℕ) :
    ∑ A ∈ range (N + 1), binomPMF N π A *
        ∑ wx ∈ antidiagonal a, binomPMF A se wx.1 * binomPMF (N - A) (1 - sp) wx.2 =
      (ProbabilityTheory.binomial N
        ⟨Bias.observedPrevalence se sp π, observedPrevalence_mem_unitInterval hse hsp hπ⟩).real
        {a} := by
  rw [binomial_thinning, ← binomPMF_eq_binomial]

end Binomial

section Likelihood

/-- The binomial likelihood of `x` apparent positives among `N` people as a function of the true
prevalence `π`, the sensitivity `se` and the specificity `sp` (Fox, MacLehose and Lash 2021,
Equation 11.4): the binomial mass at the apparent prevalence `p` of Equation 11.3. -/
noncomputable def misclassLikelihood (N x : ℕ) (se sp π : ℝ) : ℝ :=
  binomPMF N (Bias.observedPrevalence se sp π) x

/-- Equation 11.4 written out:
`L = C(N, x) [π Se + (1 - Sp)(1 - π)]^x [1 - (π Se + (1 - Sp)(1 - π))]^(N - x)`. -/
theorem misclassLikelihood_eq (N x : ℕ) (se sp π : ℝ) :
    misclassLikelihood N x se sp π =
      N.choose x * (π * se + (1 - sp) * (1 - π)) ^ x *
        (1 - (π * se + (1 - sp) * (1 - π))) ^ (N - x) := by
  have : Bias.observedPrevalence se sp π = π * se + (1 - sp) * (1 - π) := by
    rw [Bias.observedPrevalence_eq]; ring
  rw [misclassLikelihood, binomPMF, this]

/-- The likelihood depends on `(π, se, sp)` only through the apparent prevalence `p`: parameter
values with the same `p` have the same likelihood for every sample size and count. -/
theorem misclassLikelihood_congr {se sp π se' sp' π' : ℝ}
    (h : Bias.observedPrevalence se sp π = Bias.observedPrevalence se' sp' π') (N x : ℕ) :
    misclassLikelihood N x se sp π = misclassLikelihood N x se' sp' π' := by
  rw [misclassLikelihood, misclassLikelihood, h]

/-- Non-identification of the prevalence (Chapter 11, "Exposure Misclassification Using
Sensitivities and Specificities": after Equation 11.13 the text notes that the true prevalences
are not identified from the data):
for every apparent prevalence `p` in `(0, 1)` and every candidate true prevalence `π'` in
`[0, 1]` there is a classification with `se'`, `sp'` in `[0, 1]` and `se' + sp' > 1` (better than
chance) whose apparent prevalence is `p`. Explicitly `se' = p + p(1 - p)(1 - π')` and
`sp' = 1 - p + p(1 - p)π'`. Hence the data cannot exclude any prevalence. Since the likelihood
is constant on the set of parameters with a given apparent prevalence, the relative posterior
density of two points of that set is the ratio of their joint prior densities (of `π`, `se` and
`sp` together, not of `se` and `sp` alone). The witness depends on `p`: applied to cases and
controls separately it gives a differential classification. The case of one classification
shared by cases and controls, Equation 11.13, is `caseControl_not_identified`. This strengthens
`Bias.prevalence_not_identified`, which uses an uninformative classification `se + sp = 1`. -/
theorem exists_classification_of_observedPrevalence {p π' : ℝ} (hp : p ∈ Set.Ioo (0 : ℝ) 1)
    (hπ' : π' ∈ Set.Icc (0 : ℝ) 1) :
    ∃ se' sp' : ℝ, se' ∈ Set.Icc (0 : ℝ) 1 ∧ sp' ∈ Set.Icc (0 : ℝ) 1 ∧ 1 < se' + sp' ∧
      Bias.observedPrevalence se' sp' π' = p := by
  obtain ⟨h0, h1⟩ := hp
  obtain ⟨h2, h3⟩ := hπ'
  have hd : 0 < p * (1 - p) := mul_pos h0 (by linarith)
  refine ⟨p + p * (1 - p) * (1 - π'), 1 - p + p * (1 - p) * π', ⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_, ?_⟩
  · nlinarith
  · nlinarith [mul_nonneg hd.le h2]
  · nlinarith
  · nlinarith [mul_nonneg hd.le (sub_nonneg.2 h3)]
  · linarith
  · rw [Bias.observedPrevalence_eq]; ring

/-- Hence the whole likelihood function is shared: for any parameter `(π, se, sp)` with apparent
prevalence strictly between `0` and `1` and any `π'` in `[0, 1]`, some better than chance
classification `(se', sp')` makes `(π', se', sp')` give the same likelihood for every `N` and
`x`. -/
theorem exists_same_misclassLikelihood {se sp π π' : ℝ}
    (hp : Bias.observedPrevalence se sp π ∈ Set.Ioo (0 : ℝ) 1) (hπ' : π' ∈ Set.Icc (0 : ℝ) 1) :
    ∃ se' sp' : ℝ, se' ∈ Set.Icc (0 : ℝ) 1 ∧ sp' ∈ Set.Icc (0 : ℝ) 1 ∧ 1 < se' + sp' ∧
      ∀ N x, misclassLikelihood N x se' sp' π' = misclassLikelihood N x se sp π := by
  obtain ⟨se', sp', h1, h2, h3, h4⟩ := exists_classification_of_observedPrevalence hp hπ'
  exact ⟨se', sp', h1, h2, h3, fun N x => misclassLikelihood_congr h4 N x⟩

/-- The case-control likelihood of Equations 11.10 to 11.13: independent binomial counts `a` of
`N₁` cases and `c` of `N₀` controls classified as exposed, with group specific prevalences and
classification parameters (nondifferential misclassification is the case `se₁ = se₀`,
`sp₁ = sp₀`). It depends on the parameters only through the two apparent prevalences
`P₁`, `P₀` of Equation 11.12. -/
theorem caseControl_likelihood_congr {se₁ sp₁ π₁ se₀ sp₀ π₀ se₁' sp₁' π₁' se₀' sp₀' π₀' : ℝ}
    (h₁ : Bias.observedPrevalence se₁ sp₁ π₁ = Bias.observedPrevalence se₁' sp₁' π₁')
    (h₀ : Bias.observedPrevalence se₀ sp₀ π₀ = Bias.observedPrevalence se₀' sp₀' π₀')
    (N₁ a N₀ c : ℕ) :
    misclassLikelihood N₁ a se₁ sp₁ π₁ * misclassLikelihood N₀ c se₀ sp₀ π₀ =
      misclassLikelihood N₁ a se₁' sp₁' π₁' * misclassLikelihood N₀ c se₀' sp₀' π₀' := by
  rw [misclassLikelihood_congr h₁, misclassLikelihood_congr h₀]

/-- Inverting Equation 11.3 inside the admissible region: if `P ≤ se'`, `1 - P ≤ sp'` and
`se' + sp' > 1`, the prevalence `π' = (P - (1 - sp')) / (se' + sp' - 1)` lies in `[0, 1]` and has
apparent prevalence `P` under `(se', sp')`. -/
theorem prevalence_of_classification {P se' sp' : ℝ} (hse : P ≤ se') (hsp : 1 - P ≤ sp')
    (hk : 1 < se' + sp') :
    (P - (1 - sp')) / (se' + sp' - 1) ∈ Set.Icc (0 : ℝ) 1 ∧
      Bias.observedPrevalence se' sp' ((P - (1 - sp')) / (se' + sp' - 1)) = P := by
  have hk' : 0 < se' + sp' - 1 := by linarith
  refine ⟨⟨div_nonneg (by linarith) hk'.le, (div_le_one hk').2 (by linarith)⟩, ?_⟩
  rw [Bias.observedPrevalence_eq]
  field_simp
  ring

/-- **Non-identification under nondifferential misclassification** (Equation 11.13 and the text
after it). Let `(se, sp, π₁, π₀)` be any parameter with apparent prevalences `P₁`, `P₀` of cases
and controls. Every classification `(se', sp')` shared by cases and controls with
`max P₁ P₀ ≤ se'`, `1 - min P₁ P₀ ≤ sp'` and `se' + sp' > 1` (for instance any such pair in
`[0, 1]`) comes with prevalences `π₁'`, `π₀'` in `[0, 1]` for which the case-control likelihood is
the same for all data. -/
theorem caseControl_not_identified {se sp π₁ π₀ se' sp' : ℝ}
    (hse : max (Bias.observedPrevalence se sp π₁) (Bias.observedPrevalence se sp π₀) ≤ se')
    (hsp : 1 - min (Bias.observedPrevalence se sp π₁) (Bias.observedPrevalence se sp π₀) ≤ sp')
    (hk : 1 < se' + sp') :
    ∃ π₁' π₀' : ℝ, π₁' ∈ Set.Icc (0 : ℝ) 1 ∧ π₀' ∈ Set.Icc (0 : ℝ) 1 ∧
      ∀ N₁ a N₀ c : ℕ, misclassLikelihood N₁ a se sp π₁ * misclassLikelihood N₀ c se sp π₀ =
        misclassLikelihood N₁ a se' sp' π₁' * misclassLikelihood N₀ c se' sp' π₀' := by
  have m1 := min_le_left (Bias.observedPrevalence se sp π₁) (Bias.observedPrevalence se sp π₀)
  have m0 := min_le_right (Bias.observedPrevalence se sp π₁) (Bias.observedPrevalence se sp π₀)
  obtain ⟨h1, e1⟩ := prevalence_of_classification (le_trans (le_max_left _ _) hse)
    (by linarith) hk
  obtain ⟨h0, e0⟩ := prevalence_of_classification (le_trans (le_max_right _ _) hse)
    (by linarith) hk
  exact ⟨_, _, h1, h0, caseControl_likelihood_congr e1.symm e0.symm⟩

/-- A numerical instance of `caseControl_not_identified`: with apparent prevalences `0.4`
(cases) and `0.2` (controls), the shared classifications `se = sp = 0.95` with prevalences
`(7/18, 1/6)` and `se = sp = 0.9` with prevalences `(3/8, 1/8)` have the same case-control
likelihood for all data, but true odds ratios `35/11` and `21/5`. -/
theorem caseControl_not_identified_example :
    Bias.observedPrevalence 0.95 0.95 (7 / 18) = 0.4 ∧
      Bias.observedPrevalence 0.95 0.95 (1 / 6) = 0.2 ∧
      Bias.observedPrevalence 0.9 0.9 (3 / 8) = 0.4 ∧
      Bias.observedPrevalence 0.9 0.9 (1 / 8) = 0.2 ∧
      (∀ N₁ a N₀ c : ℕ,
        misclassLikelihood N₁ a 0.95 0.95 (7 / 18) * misclassLikelihood N₀ c 0.95 0.95 (1 / 6) =
          misclassLikelihood N₁ a 0.9 0.9 (3 / 8) * misclassLikelihood N₀ c 0.9 0.9 (1 / 8)) ∧
      (7 / 18 / (1 - 7 / 18)) / (1 / 6 / (1 - 1 / 6)) = (35 / 11 : ℝ) ∧
      (3 / 8 / (1 - 3 / 8)) / (1 / 8 / (1 - 1 / 8)) = (21 / 5 : ℝ) := by
  have e1 : Bias.observedPrevalence 0.95 0.95 (7 / 18) = 0.4 := by
    rw [Bias.observedPrevalence_eq]; norm_num
  have e2 : Bias.observedPrevalence 0.95 0.95 (1 / 6) = 0.2 := by
    rw [Bias.observedPrevalence_eq]; norm_num
  have e3 : Bias.observedPrevalence 0.9 0.9 (3 / 8) = 0.4 := by
    rw [Bias.observedPrevalence_eq]; norm_num
  have e4 : Bias.observedPrevalence 0.9 0.9 (1 / 8) = 0.2 := by
    rw [Bias.observedPrevalence_eq]; norm_num
  refine ⟨e1, e2, e3, e4, fun N₁ a N₀ c => caseControl_likelihood_congr (e1.trans e3.symm)
    (e2.trans e4.symm) N₁ a N₀ c, by norm_num, by norm_num⟩

/-- A concrete instance: `(π, se, sp) = (0.2, 0.9, 0.9)` and `(0.25, 0.8, 0.92)` both have
apparent prevalence `0.26`, so they have the same likelihood for all data although the true
prevalences differ. -/
theorem misclassLikelihood_example (N x : ℕ) :
    misclassLikelihood N x 0.9 0.9 0.2 = misclassLikelihood N x 0.8 0.92 0.25 := by
  apply misclassLikelihood_congr
  rw [Bias.observedPrevalence_eq, Bias.observedPrevalence_eq]
  norm_num

end Likelihood

section Conjugacy

open ProbabilityTheory MeasureTheory

/-- The beta kernel identity behind every conjugate update: multiplying the `Beta(α, β)` density
by `x^m (1 - x)^l` gives the `Beta(α + m, β + l)` density times the constant
`B(α + m, β + l) / B(α, β)`. Both sides vanish off `(0, 1)`. -/
theorem betaPDFReal_mul_pow (α β x : ℝ) (hα : 0 < α) (hβ : 0 < β) (m l : ℕ) :
    betaPDFReal α β x * (x ^ m * (1 - x) ^ l) =
      beta (α + m) (β + l) / beta α β * betaPDFReal (α + m) (β + l) x := by
  unfold betaPDFReal
  split_ifs with hx
  · obtain ⟨hx0, hx1⟩ := hx
    have h1 : (0 : ℝ) < 1 - x := by linarith
    have hB := beta_pos hα hβ
    have hB' := beta_pos (by positivity : 0 < α + m) (by positivity : 0 < β + l)
    have e1 : x ^ (α + m - 1) = x ^ (α - 1) * x ^ m := by
      rw [show α + m - 1 = (α - 1) + m by ring, Real.rpow_add_natCast hx0.ne']
    have e2 : (1 - x) ^ (β + l - 1) = (1 - x) ^ (β - 1) * (1 - x) ^ l := by
      rw [show β + l - 1 = (β - 1) + l by ring, Real.rpow_add_natCast h1.ne']
    rw [e1, e2]
    field_simp
  · simp

/-- Beta and binomial conjugacy, density form (Fox, MacLehose and Lash 2021, Chapter 11: the
beta prior of Equation 11.5 combined with the binomial likelihood of Equation 11.2 through
Bayes' theorem, Equation 11.7). The `Beta(α, β)` prior density times the binomial likelihood of
`k` successes in `n` trials equals the marginal likelihood
`C(n, k) B(α + k, β + n - k) / B(α, β)` times the `Beta(α + k, β + n - k)` density. The
identity is meant for `k ≤ n`; for `k > n` both sides vanish because `C(n, k) = 0`. -/
theorem betaPDFReal_mul_binomPMF (α β : ℝ) (hα : 0 < α) (hβ : 0 < β) (n k : ℕ) (x : ℝ) :
    betaPDFReal α β x * binomPMF n x k =
      n.choose k * (beta (α + k) (β + (n - k : ℕ)) / beta α β) *
        betaPDFReal (α + k) (β + (n - k : ℕ)) x := by
  have h := betaPDFReal_mul_pow α β x hα hβ k (n - k)
  calc betaPDFReal α β x * binomPMF n x k
      = n.choose k * (betaPDFReal α β x * (x ^ k * (1 - x) ^ (n - k))) := by
        unfold binomPMF; ring
    _ = _ := by rw [h]; ring

/-- The marginal likelihood `C(n, k) B(α + k, β + n - k) / B(α, β)` of the beta and binomial
model is positive when `k ≤ n`. -/
theorem betaBinomial_marginal_pos (α β : ℝ) (hα : 0 < α) (hβ : 0 < β) {n k : ℕ} (hk : k ≤ n) :
    0 < (n.choose k : ℝ) * (beta (α + k) (β + (n - k : ℕ)) / beta α β) := by
  have := Nat.choose_pos hk
  have hB := beta_pos hα hβ
  have hB' := beta_pos (by positivity : 0 < α + k) (by positivity : 0 < β + (n - k : ℕ))
  positivity

/-- Beta and binomial conjugacy, measure form. Reweighting the `Beta(α, β)` prior measure by the
binomial likelihood `x ↦ C(n, k) x^k (1 - x)^(n - k)` gives the marginal likelihood times the
`Beta(α + k, β + n - k)` measure. As above it is meant for `k ≤ n` (for `k > n` both sides are
zero); `betaBinomial_posterior` assumes `k ≤ n`. -/
theorem betaMeasure_withDensity_binomPMF (α β : ℝ) (hα : 0 < α) (hβ : 0 < β) (n k : ℕ) :
    (betaMeasure α β).withDensity (fun x => ENNReal.ofReal (binomPMF n x k)) =
      ENNReal.ofReal (n.choose k * (beta (α + k) (β + (n - k : ℕ)) / beta α β)) •
        betaMeasure (α + k) (β + (n - k : ℕ)) := by
  have hlik : Measurable fun x : ℝ => ENNReal.ofReal (binomPMF n x k) := by
    unfold binomPMF; fun_prop
  have hpdf : ∀ a b : ℝ, Measurable (betaPDF a b) := fun a b =>
    (measurable_betaPDFReal a b).ennreal_ofReal
  unfold betaMeasure
  rw [← withDensity_mul _ (hpdf α β) hlik, ← withDensity_smul _ (hpdf _ _)]
  congr 1
  funext x
  have hB := beta_pos hα hβ
  have hB' := beta_pos (by positivity : 0 < α + k) (by positivity : 0 < β + (n - k : ℕ))
  have hc : 0 ≤ (n.choose k : ℝ) * (beta (α + k) (β + (n - k : ℕ)) / beta α β) := by positivity
  have hp : 0 ≤ betaPDFReal α β x := by
    unfold betaPDFReal; split_ifs with h
    · have h1 : 0 < 1 - x := by linarith [h.2]
      have := Real.rpow_nonneg h.1.le (α - 1)
      have := Real.rpow_nonneg h1.le (β - 1)
      positivity
    · exact le_rfl
  simp only [Pi.mul_apply, Pi.smul_apply, smul_eq_mul, betaPDF]
  rw [← ENNReal.ofReal_mul hp, ← ENNReal.ofReal_mul hc, betaPDFReal_mul_binomPMF α β hα hβ]

/-- Bayes' theorem for the beta and binomial model (Equation 11.7): the prior reweighted by the
likelihood has total mass equal to the marginal likelihood
`C(n, k) B(α + k, β + n - k) / B(α, β)`, and dividing by it gives exactly the
`Beta(α + k, β + n - k)` posterior. -/
theorem betaBinomial_posterior (α β : ℝ) (hα : 0 < α) (hβ : 0 < β) {n k : ℕ} (hk : k ≤ n) :
    (betaMeasure α β).withDensity (fun x => ENNReal.ofReal (binomPMF n x k)) Set.univ =
        ENNReal.ofReal (n.choose k * (beta (α + k) (β + (n - k : ℕ)) / beta α β)) ∧
      (ENNReal.ofReal (n.choose k * (beta (α + k) (β + (n - k : ℕ)) / beta α β)))⁻¹ •
          (betaMeasure α β).withDensity (fun x => ENNReal.ofReal (binomPMF n x k)) =
        betaMeasure (α + k) (β + (n - k : ℕ)) := by
  have hc := betaBinomial_marginal_pos α β hα hβ hk
  have hprob := isProbabilityMeasureBeta (α := α + k) (β := β + (n - k : ℕ)) (by positivity)
    (by positivity)
  rw [betaMeasure_withDensity_binomPMF α β hα hβ n k]
  refine ⟨?_, ?_⟩
  · simp
  · rw [smul_smul, ENNReal.inv_mul_cancel (ENNReal.ofReal_pos.2 hc).ne' ENNReal.ofReal_ne_top,
      one_smul]

end Conjugacy

section Gibbs

open ProbabilityTheory

/-! ### Gibbs full conditionals

The latent model of the Chapter 11 appendix ("Appendix: Justification for Probabilistic Bias
Analysis for Exposure Misclassification in a Case-Control Study", Tables 11.7 and 11.8), for one
group (cases or controls) of size `N`: the latent cells `W` (truly and apparently exposed), `X`
(truly unexposed, apparently exposed), `Y` (truly exposed, apparently unexposed) and `Z` (truly
and apparently unexposed) are multinomial with cell probabilities `se π`, `(1 - sp)(1 - π)`,
`(1 - se) π` and `sp (1 - π)`, and `π ~ Beta(εa, εb)`, `se ~ Beta(α, β)`, `sp ~ Beta(γ, δ)`. The
observed counts are `a = W + X` and `b = Y + Z`. -/

/-- The multinomial likelihood kernel `p₁^W p₂^X p₃^Y p₄^Z` of the latent cells. -/
def latentLik (se sp π : ℝ) (W X Y Z : ℕ) : ℝ :=
  (se * π) ^ W * ((1 - sp) * (1 - π)) ^ X * ((1 - se) * π) ^ Y * (sp * (1 - π)) ^ Z

/-- The multinomial coefficient `(W + X + Y + Z)! / (W! X! Y! Z!)`. -/
noncomputable def multinomCoeff (W X Y Z : ℕ) : ℝ :=
  ((W + X + Y + Z).factorial : ℝ) / (W.factorial * X.factorial * Y.factorial * Z.factorial)

/-- The joint density of the parameters and latent cells (prior densities times the multinomial
probability), the target of the Gibbs sampler. -/
noncomputable def gibbsJoint (α β γ δ εa εb se sp π : ℝ) (W X Y Z : ℕ) : ℝ :=
  betaPDFReal α β se * betaPDFReal γ δ sp * betaPDFReal εa εb π * multinomCoeff W X Y Z *
    latentLik se sp π W X Y Z

/-- The multinomial kernel factorizes into a sensitivity part, a specificity part and a
prevalence part: `se^W (1 - se)^Y · sp^Z (1 - sp)^X · π^(W + Y) (1 - π)^(X + Z)`. -/
theorem latentLik_factor (se sp π : ℝ) (W X Y Z : ℕ) :
    latentLik se sp π W X Y Z =
      (se ^ W * (1 - se) ^ Y) * (sp ^ Z * (1 - sp) ^ X) * (π ^ (W + Y) * (1 - π) ^ (X + Z)) := by
  unfold latentLik
  rw [mul_pow, mul_pow, mul_pow, mul_pow, pow_add, pow_add]
  ring

/-- Full conditional of the sensitivity: as a function of `se`, the joint density is a constant
(depending only on the other variables) times the `Beta(α + W, β + Y)` density. -/
theorem gibbsJoint_se (α β γ δ εa εb se sp π : ℝ) (hα : 0 < α) (hβ : 0 < β) (W X Y Z : ℕ) :
    gibbsJoint α β γ δ εa εb se sp π W X Y Z =
      (beta (α + W) (β + Y) / beta α β * betaPDFReal γ δ sp * betaPDFReal εa εb π *
          multinomCoeff W X Y Z * (sp ^ Z * (1 - sp) ^ X) *
          (π ^ (W + Y) * (1 - π) ^ (X + Z))) *
        betaPDFReal (α + W) (β + Y) se := by
  have h := betaPDFReal_mul_pow α β se hα hβ W Y
  unfold gibbsJoint
  rw [latentLik_factor]
  linear_combination (betaPDFReal γ δ sp * betaPDFReal εa εb π * multinomCoeff W X Y Z *
    (sp ^ Z * (1 - sp) ^ X) * (π ^ (W + Y) * (1 - π) ^ (X + Z))) * h

/-- Full conditional of the specificity: the `Beta(γ + Z, δ + X)` density times a constant. -/
theorem gibbsJoint_sp (α β γ δ εa εb se sp π : ℝ) (hγ : 0 < γ) (hδ : 0 < δ) (W X Y Z : ℕ) :
    gibbsJoint α β γ δ εa εb se sp π W X Y Z =
      (beta (γ + Z) (δ + X) / beta γ δ * betaPDFReal α β se * betaPDFReal εa εb π *
          multinomCoeff W X Y Z * (se ^ W * (1 - se) ^ Y) *
          (π ^ (W + Y) * (1 - π) ^ (X + Z))) *
        betaPDFReal (γ + Z) (δ + X) sp := by
  have h := betaPDFReal_mul_pow γ δ sp hγ hδ Z X
  unfold gibbsJoint
  rw [latentLik_factor]
  linear_combination (betaPDFReal α β se * betaPDFReal εa εb π * multinomCoeff W X Y Z *
    (se ^ W * (1 - se) ^ Y) * (π ^ (W + Y) * (1 - π) ^ (X + Z))) * h

/-- Full conditional of the prevalence: the `Beta(εa + W + Y, εb + X + Z)` density times a
constant. -/
theorem gibbsJoint_prevalence (α β γ δ εa εb se sp π : ℝ) (ha : 0 < εa) (hb : 0 < εb)
    (W X Y Z : ℕ) :
    gibbsJoint α β γ δ εa εb se sp π W X Y Z =
      (beta (εa + (W + Y : ℕ)) (εb + (X + Z : ℕ)) / beta εa εb * betaPDFReal α β se *
          betaPDFReal γ δ sp * multinomCoeff W X Y Z * (se ^ W * (1 - se) ^ Y) *
          (sp ^ Z * (1 - sp) ^ X)) *
        betaPDFReal (εa + (W + Y : ℕ)) (εb + (X + Z : ℕ)) π := by
  have h := betaPDFReal_mul_pow εa εb π ha hb (W + Y) (X + Z)
  unfold gibbsJoint
  rw [latentLik_factor]
  linear_combination (betaPDFReal α β se * betaPDFReal γ δ sp * multinomCoeff W X Y Z *
    (se ^ W * (1 - se) ^ Y) * (sp ^ Z * (1 - sp) ^ X)) * h

/-- Splitting a binomial kernel: for `W ≤ a` and `u + v ≠ 0`,
`C(a, W) u^W v^(a - W) = (u + v)^a · Bin(a, u / (u + v)) {W}`. -/
theorem choose_mul_pow_eq_binomPMF {a W : ℕ} (hW : W ≤ a) {u v : ℝ} (huv : u + v ≠ 0) :
    a.choose W * u ^ W * v ^ (a - W) = (u + v) ^ a * binomPMF a (u / (u + v)) W := by
  have h1 : 1 - u / (u + v) = v / (u + v) := by field_simp; ring
  have h2 : (u + v) ^ a = (u + v) ^ W * (u + v) ^ (a - W) := by
    rw [← pow_add, Nat.add_sub_cancel' hW]
  rw [binomPMF, h1, div_pow, div_pow, h2]
  field_simp

/-- The multinomial coefficient with `X = a - W` splits as the coefficient of the observed margin
times `C(a, W)`. -/
theorem multinomCoeff_sub_left {a W : ℕ} (hW : W ≤ a) (Y Z : ℕ) :
    multinomCoeff W (a - W) Y Z = multinomCoeff a 0 Y Z * a.choose W := by
  have h := Nat.choose_mul_factorial_mul_factorial hW
  have h' : (a.choose W : ℝ) * W.factorial * (a - W).factorial = a.factorial := by
    exact_mod_cast h
  have hW' : W + (a - W) = a := Nat.add_sub_cancel' hW
  unfold multinomCoeff
  rw [hW', Nat.add_zero, Nat.factorial_zero, Nat.cast_one, mul_one]
  have := Nat.factorial_pos W
  have := Nat.factorial_pos (a - W)
  have := Nat.factorial_pos Y
  have := Nat.factorial_pos Z
  have := Nat.choose_pos hW
  rw [← h']
  field_simp

/-- Full conditional of `W` given the observed `a = W + X`: with `p₁ = se π` and
`p₂ = (1 - sp)(1 - π)`, the joint density as a function of `W` (with `X = a - W`) is a constant
times `Bin(a, ppv) {W}`, where `ppv = se π / (se π + (1 - sp)(1 - π))`. -/
theorem gibbsJoint_W (α β γ δ εa εb se sp π : ℝ)
    (hppv : se * π + (1 - sp) * (1 - π) ≠ 0) {a W : ℕ} (hW : W ≤ a) (Y Z : ℕ) :
    gibbsJoint α β γ δ εa εb se sp π W (a - W) Y Z =
      (betaPDFReal α β se * betaPDFReal γ δ sp * betaPDFReal εa εb π * multinomCoeff a 0 Y Z *
          (se * π + (1 - sp) * (1 - π)) ^ a * ((1 - se) * π) ^ Y * (sp * (1 - π)) ^ Z) *
        binomPMF a (se * π / (se * π + (1 - sp) * (1 - π))) W := by
  have h := choose_mul_pow_eq_binomPMF hW hppv
  unfold gibbsJoint latentLik
  rw [multinomCoeff_sub_left hW]
  linear_combination (betaPDFReal α β se * betaPDFReal γ δ sp * betaPDFReal εa εb π *
    multinomCoeff a 0 Y Z * ((1 - se) * π) ^ Y * (sp * (1 - π)) ^ Z) * h

/-- The multinomial coefficient with `Y = b - Z` splits as the coefficient of the observed margin
times `C(b, Z)`. -/
theorem multinomCoeff_sub_right (W X : ℕ) {b Z : ℕ} (hZ : Z ≤ b) :
    multinomCoeff W X (b - Z) Z = multinomCoeff W X b 0 * b.choose Z := by
  have h := Nat.choose_mul_factorial_mul_factorial hZ
  have h' : (b.choose Z : ℝ) * Z.factorial * (b - Z).factorial = b.factorial := by
    exact_mod_cast h
  have hZ' : W + X + (b - Z) + Z = W + X + b + 0 := by omega
  unfold multinomCoeff
  rw [hZ', Nat.factorial_zero, Nat.cast_one, mul_one]
  have := Nat.factorial_pos W
  have := Nat.factorial_pos X
  have := Nat.factorial_pos Z
  have := Nat.factorial_pos (b - Z)
  have := Nat.choose_pos hZ
  rw [← h']
  field_simp

/-- Full conditional of `Z` given the observed `b = Y + Z`: a constant times `Bin(b, npv) {Z}`,
where `npv = sp (1 - π) / (sp (1 - π) + (1 - se) π)`. -/
theorem gibbsJoint_Z (α β γ δ εa εb se sp π : ℝ)
    (hnpv : sp * (1 - π) + (1 - se) * π ≠ 0) (W X : ℕ) {b Z : ℕ} (hZ : Z ≤ b) :
    gibbsJoint α β γ δ εa εb se sp π W X (b - Z) Z =
      (betaPDFReal α β se * betaPDFReal γ δ sp * betaPDFReal εa εb π * multinomCoeff W X b 0 *
          (se * π) ^ W * ((1 - sp) * (1 - π)) ^ X * (sp * (1 - π) + (1 - se) * π) ^ b) *
        binomPMF b (sp * (1 - π) / (sp * (1 - π) + (1 - se) * π)) Z := by
  have h := choose_mul_pow_eq_binomPMF hZ hnpv
  unfold gibbsJoint latentLik
  rw [multinomCoeff_sub_right W X hZ]
  linear_combination (betaPDFReal α β se * betaPDFReal γ δ sp * betaPDFReal εa εb π *
    multinomCoeff W X b 0 * (se * π) ^ W * ((1 - sp) * (1 - π)) ^ X) * h

/-- Sampling `Y ~ Bin(b, 1 - npv)` and setting `Z = b - Y` is the same as sampling
`Z ~ Bin(b, npv)`: `Bin(b, 1 - q) {Y} = Bin(b, q) {b - Y}` for `Y ≤ b`. This is why the
probabilistic bias analysis of Chapter 8, which samples `Y`, agrees with the Gibbs step, which
samples `Z`. -/
theorem binomPMF_one_sub {b Y : ℕ} (hY : Y ≤ b) (q : ℝ) :
    binomPMF b (1 - q) Y = binomPMF b q (b - Y) := by
  rw [binomPMF, binomPMF, Nat.choose_symm hY, Nat.sub_sub_self hY, sub_sub_cancel]
  ring

/-- Nondifferential misclassification pools the counts: with one sensitivity shared by cases
(cells `W₁, X₁, Y₁, Z₁`, prevalence `π₁`) and controls (`W₀, X₀, Y₀, Z₀`, `π₀`), the prior
density of `se` times both multinomial kernels is a constant times the
`Beta(α + W₁ + W₀, β + Y₁ + Y₀)` density. -/
theorem nondifferential_se (α β se sp π₁ π₀ : ℝ) (hα : 0 < α) (hβ : 0 < β)
    (W₁ X₁ Y₁ Z₁ W₀ X₀ Y₀ Z₀ : ℕ) :
    betaPDFReal α β se * latentLik se sp π₁ W₁ X₁ Y₁ Z₁ * latentLik se sp π₀ W₀ X₀ Y₀ Z₀ =
      (beta (α + (W₁ + W₀ : ℕ)) (β + (Y₁ + Y₀ : ℕ)) / beta α β *
          ((sp ^ Z₁ * (1 - sp) ^ X₁) * (π₁ ^ (W₁ + Y₁) * (1 - π₁) ^ (X₁ + Z₁))) *
          ((sp ^ Z₀ * (1 - sp) ^ X₀) * (π₀ ^ (W₀ + Y₀) * (1 - π₀) ^ (X₀ + Z₀)))) *
        betaPDFReal (α + (W₁ + W₀ : ℕ)) (β + (Y₁ + Y₀ : ℕ)) se := by
  have h := betaPDFReal_mul_pow α β se hα hβ (W₁ + W₀) (Y₁ + Y₀)
  rw [latentLik_factor, latentLik_factor]
  rw [pow_add se, pow_add (1 - se)] at h
  linear_combination ((sp ^ Z₁ * (1 - sp) ^ X₁) * (π₁ ^ (W₁ + Y₁) * (1 - π₁) ^ (X₁ + Z₁)) *
    ((sp ^ Z₀ * (1 - sp) ^ X₀) * (π₀ ^ (W₀ + Y₀) * (1 - π₀) ^ (X₀ + Z₀)))) * h

/-- Nondifferential misclassification, specificity: a constant times the
`Beta(γ + Z₁ + Z₀, δ + X₁ + X₀)` density. -/
theorem nondifferential_sp (γ δ se sp π₁ π₀ : ℝ) (hγ : 0 < γ) (hδ : 0 < δ)
    (W₁ X₁ Y₁ Z₁ W₀ X₀ Y₀ Z₀ : ℕ) :
    betaPDFReal γ δ sp * latentLik se sp π₁ W₁ X₁ Y₁ Z₁ * latentLik se sp π₀ W₀ X₀ Y₀ Z₀ =
      (beta (γ + (Z₁ + Z₀ : ℕ)) (δ + (X₁ + X₀ : ℕ)) / beta γ δ *
          ((se ^ W₁ * (1 - se) ^ Y₁) * (π₁ ^ (W₁ + Y₁) * (1 - π₁) ^ (X₁ + Z₁))) *
          ((se ^ W₀ * (1 - se) ^ Y₀) * (π₀ ^ (W₀ + Y₀) * (1 - π₀) ^ (X₀ + Z₀)))) *
        betaPDFReal (γ + (Z₁ + Z₀ : ℕ)) (δ + (X₁ + X₀ : ℕ)) sp := by
  have h := betaPDFReal_mul_pow γ δ sp hγ hδ (Z₁ + Z₀) (X₁ + X₀)
  rw [latentLik_factor, latentLik_factor]
  rw [pow_add sp, pow_add (1 - sp)] at h
  linear_combination ((se ^ W₁ * (1 - se) ^ Y₁) * (π₁ ^ (W₁ + Y₁) * (1 - π₁) ^ (X₁ + Z₁)) *
    ((se ^ W₀ * (1 - se) ^ Y₀) * (π₀ ^ (W₀ + Y₀) * (1 - π₀) ^ (X₀ + Z₀)))) * h

/-! ### Normalized full conditionals

The identities above are proportionality statements: the constant can vanish (for instance at a
conditioning value outside `(0, 1)`) and the binomial parameters can leave `[0, 1]` when the
conditioning values do. Below, with positive prior shapes and conditioning values in `(0, 1)`, the
constants are positive and each slice of the joint density, normalized by its total mass, is the
stated beta law or the stated product of binomial laws. -/

open MeasureTheory

/-- A density that is a positive constant times a beta density defines a finite measure with
total mass that constant, and normalizing it gives the beta law. -/
theorem withDensity_const_mul_betaPDFReal {f : ℝ → ℝ} {c a b : ℝ} (hc : 0 < c) (ha : 0 < a)
    (hb : 0 < b) (hf : ∀ x, f x = c * betaPDFReal a b x) :
    volume.withDensity (fun x => ENNReal.ofReal (f x)) Set.univ = ENNReal.ofReal c ∧
      (volume.withDensity (fun x => ENNReal.ofReal (f x)) Set.univ)⁻¹ •
          volume.withDensity (fun x => ENNReal.ofReal (f x)) = betaMeasure a b := by
  have hprob := isProbabilityMeasureBeta ha hb
  have hμ : volume.withDensity (fun x => ENNReal.ofReal (f x)) =
      ENNReal.ofReal c • betaMeasure a b := by
    have hpdf : Measurable (betaPDF a b) := (measurable_betaPDFReal a b).ennreal_ofReal
    unfold betaMeasure
    rw [← withDensity_smul _ hpdf]
    congr 1
    funext x
    simp only [hf, Pi.smul_apply, smul_eq_mul, betaPDF, ENNReal.ofReal_mul hc.le]
  have huniv : volume.withDensity (fun x => ENNReal.ofReal (f x)) Set.univ = ENNReal.ofReal c := by
    rw [hμ, smul_apply, measure_univ, smul_eq_mul, mul_one]
  refine ⟨huniv, ?_⟩
  rw [huniv, hμ, smul_smul, ENNReal.inv_mul_cancel (ENNReal.ofReal_pos.2 hc).ne'
    ENNReal.ofReal_ne_top, one_smul]

/-- The multinomial coefficient is positive. -/
theorem multinomCoeff_pos (W X Y Z : ℕ) : 0 < multinomCoeff W X Y Z := by
  unfold multinomCoeff
  positivity

/-- The kernel `x^m (1 - x)^l` is positive on `(0, 1)`. -/
theorem pow_mul_one_sub_pow_pos {x : ℝ} (hx : x ∈ Set.Ioo (0 : ℝ) 1) (m l : ℕ) :
    0 < x ^ m * (1 - x) ^ l :=
  mul_pos (pow_pos hx.1 m) (pow_pos (sub_pos.2 hx.2) l)

/-- **Normalized full conditional of the sensitivity.** With positive prior shapes and the
conditioning values `sp`, `π` in `(0, 1)`, the slice `se ↦ gibbsJoint … se sp π W X Y Z` of the
joint density has positive finite total mass `c`, and normalizing it gives `Beta(α + W, β + Y)`. -/
theorem gibbs_se_conditional {α β γ δ εa εb sp π : ℝ} (hα : 0 < α) (hβ : 0 < β) (hγ : 0 < γ)
    (hδ : 0 < δ) (ha : 0 < εa) (hb : 0 < εb) (hsp : sp ∈ Set.Ioo (0 : ℝ) 1)
    (hπ : π ∈ Set.Ioo (0 : ℝ) 1) (W X Y Z : ℕ) :
    let μ := volume.withDensity fun se => ENNReal.ofReal (gibbsJoint α β γ δ εa εb se sp π W X Y Z)
    ∃ c : ℝ, 0 < c ∧ μ Set.univ = ENNReal.ofReal c ∧
      (μ Set.univ)⁻¹ • μ = betaMeasure (α + W) (β + Y) := by
  intro μ
  have hB := beta_pos hα hβ
  have hB' := beta_pos (by positivity : 0 < α + W) (by positivity : 0 < β + Y)
  have h1 := betaPDFReal_pos hsp.1 hsp.2 hγ hδ
  have h2 := betaPDFReal_pos hπ.1 hπ.2 ha hb
  have h3 := multinomCoeff_pos W X Y Z
  have h4 := pow_mul_one_sub_pow_pos hsp Z X
  have h5 := pow_mul_one_sub_pow_pos hπ (W + Y) (X + Z)
  refine ⟨_, by positivity, withDensity_const_mul_betaPDFReal (by positivity) (by positivity)
    (by positivity) fun se => gibbsJoint_se α β γ δ εa εb se sp π hα hβ W X Y Z⟩

/-- **Normalized full conditional of the specificity**: with positive prior shapes and `se`, `π`
in `(0, 1)`, the slice in `sp` has positive finite total mass and normalizes to
`Beta(γ + Z, δ + X)`. -/
theorem gibbs_sp_conditional {α β γ δ εa εb se π : ℝ} (hα : 0 < α) (hβ : 0 < β) (hγ : 0 < γ)
    (hδ : 0 < δ) (ha : 0 < εa) (hb : 0 < εb) (hse : se ∈ Set.Ioo (0 : ℝ) 1)
    (hπ : π ∈ Set.Ioo (0 : ℝ) 1) (W X Y Z : ℕ) :
    let μ := volume.withDensity fun sp => ENNReal.ofReal (gibbsJoint α β γ δ εa εb se sp π W X Y Z)
    ∃ c : ℝ, 0 < c ∧ μ Set.univ = ENNReal.ofReal c ∧
      (μ Set.univ)⁻¹ • μ = betaMeasure (γ + Z) (δ + X) := by
  intro μ
  have hB := beta_pos hγ hδ
  have hB' := beta_pos (by positivity : 0 < γ + Z) (by positivity : 0 < δ + X)
  have h1 := betaPDFReal_pos hse.1 hse.2 hα hβ
  have h2 := betaPDFReal_pos hπ.1 hπ.2 ha hb
  have h3 := multinomCoeff_pos W X Y Z
  have h4 := pow_mul_one_sub_pow_pos hse W Y
  have h5 := pow_mul_one_sub_pow_pos hπ (W + Y) (X + Z)
  refine ⟨_, by positivity, withDensity_const_mul_betaPDFReal (by positivity) (by positivity)
    (by positivity) fun sp => gibbsJoint_sp α β γ δ εa εb se sp π hγ hδ W X Y Z⟩

/-- **Normalized full conditional of the prevalence**: with positive prior shapes and `se`, `sp`
in `(0, 1)`, the slice in `π` has positive finite total mass and normalizes to
`Beta(εa + W + Y, εb + X + Z)`. -/
theorem gibbs_prevalence_conditional {α β γ δ εa εb se sp : ℝ} (hα : 0 < α) (hβ : 0 < β)
    (hγ : 0 < γ) (hδ : 0 < δ) (ha : 0 < εa) (hb : 0 < εb) (hse : se ∈ Set.Ioo (0 : ℝ) 1)
    (hsp : sp ∈ Set.Ioo (0 : ℝ) 1) (W X Y Z : ℕ) :
    let μ := volume.withDensity fun π => ENNReal.ofReal (gibbsJoint α β γ δ εa εb se sp π W X Y Z)
    ∃ c : ℝ, 0 < c ∧ μ Set.univ = ENNReal.ofReal c ∧
      (μ Set.univ)⁻¹ • μ = betaMeasure (εa + (W + Y : ℕ)) (εb + (X + Z : ℕ)) := by
  intro μ
  have hB := beta_pos ha hb
  have hB' := beta_pos (by positivity : 0 < εa + (W + Y : ℕ)) (by positivity : 0 < εb + (X + Z : ℕ))
  have h1 := betaPDFReal_pos hse.1 hse.2 hα hβ
  have h2 := betaPDFReal_pos hsp.1 hsp.2 hγ hδ
  have h3 := multinomCoeff_pos W X Y Z
  have h4 := pow_mul_one_sub_pow_pos hse W Y
  have h5 := pow_mul_one_sub_pow_pos hsp Z X
  refine ⟨_, by positivity, withDensity_const_mul_betaPDFReal (by positivity) (by positivity)
    (by positivity) fun π => gibbsJoint_prevalence α β γ δ εa εb se sp π ha hb W X Y Z⟩

/-- **Normalized pooled conditional of the sensitivity** (nondifferential misclassification):
with positive prior shapes and `sp`, `π₁`, `π₀` in `(0, 1)`, the prior density of `se` times both
multinomial kernels has positive finite total mass and normalizes to
`Beta(α + W₁ + W₀, β + Y₁ + Y₀)`. -/
theorem nondifferential_se_conditional {α β sp π₁ π₀ : ℝ} (hα : 0 < α) (hβ : 0 < β)
    (hsp : sp ∈ Set.Ioo (0 : ℝ) 1) (hπ₁ : π₁ ∈ Set.Ioo (0 : ℝ) 1) (hπ₀ : π₀ ∈ Set.Ioo (0 : ℝ) 1)
    (W₁ X₁ Y₁ Z₁ W₀ X₀ Y₀ Z₀ : ℕ) :
    let μ := volume.withDensity fun se => ENNReal.ofReal
      (betaPDFReal α β se * latentLik se sp π₁ W₁ X₁ Y₁ Z₁ * latentLik se sp π₀ W₀ X₀ Y₀ Z₀)
    ∃ c : ℝ, 0 < c ∧ μ Set.univ = ENNReal.ofReal c ∧
      (μ Set.univ)⁻¹ • μ = betaMeasure (α + (W₁ + W₀ : ℕ)) (β + (Y₁ + Y₀ : ℕ)) := by
  intro μ
  have hB := beta_pos hα hβ
  have hB' := beta_pos (by positivity : 0 < α + (W₁ + W₀ : ℕ))
    (by positivity : 0 < β + (Y₁ + Y₀ : ℕ))
  have h1 := pow_mul_one_sub_pow_pos hsp Z₁ X₁
  have h2 := pow_mul_one_sub_pow_pos hsp Z₀ X₀
  have h3 := pow_mul_one_sub_pow_pos hπ₁ (W₁ + Y₁) (X₁ + Z₁)
  have h4 := pow_mul_one_sub_pow_pos hπ₀ (W₀ + Y₀) (X₀ + Z₀)
  refine ⟨_, by positivity, withDensity_const_mul_betaPDFReal (by positivity) (by positivity)
    (by positivity) fun se => nondifferential_se α β se sp π₁ π₀ hα hβ W₁ X₁ Y₁ Z₁ W₀ X₀ Y₀ Z₀⟩

/-- **Normalized pooled conditional of the specificity**: with positive prior shapes and `se`,
`π₁`, `π₀` in `(0, 1)`, the slice normalizes to `Beta(γ + Z₁ + Z₀, δ + X₁ + X₀)`. -/
theorem nondifferential_sp_conditional {γ δ se π₁ π₀ : ℝ} (hγ : 0 < γ) (hδ : 0 < δ)
    (hse : se ∈ Set.Ioo (0 : ℝ) 1) (hπ₁ : π₁ ∈ Set.Ioo (0 : ℝ) 1) (hπ₀ : π₀ ∈ Set.Ioo (0 : ℝ) 1)
    (W₁ X₁ Y₁ Z₁ W₀ X₀ Y₀ Z₀ : ℕ) :
    let μ := volume.withDensity fun sp => ENNReal.ofReal
      (betaPDFReal γ δ sp * latentLik se sp π₁ W₁ X₁ Y₁ Z₁ * latentLik se sp π₀ W₀ X₀ Y₀ Z₀)
    ∃ c : ℝ, 0 < c ∧ μ Set.univ = ENNReal.ofReal c ∧
      (μ Set.univ)⁻¹ • μ = betaMeasure (γ + (Z₁ + Z₀ : ℕ)) (δ + (X₁ + X₀ : ℕ)) := by
  intro μ
  have hB := beta_pos hγ hδ
  have hB' := beta_pos (by positivity : 0 < γ + (Z₁ + Z₀ : ℕ))
    (by positivity : 0 < δ + (X₁ + X₀ : ℕ))
  have h1 := pow_mul_one_sub_pow_pos hse W₁ Y₁
  have h2 := pow_mul_one_sub_pow_pos hse W₀ Y₀
  have h3 := pow_mul_one_sub_pow_pos hπ₁ (W₁ + Y₁) (X₁ + Z₁)
  have h4 := pow_mul_one_sub_pow_pos hπ₀ (W₀ + Y₀) (X₀ + Z₀)
  refine ⟨_, by positivity, withDensity_const_mul_betaPDFReal (by positivity) (by positivity)
    (by positivity) fun sp => nondifferential_sp γ δ se sp π₁ π₀ hγ hδ W₁ X₁ Y₁ Z₁ W₀ X₀ Y₀ Z₀⟩

/-- The binomial probabilities sum to one: `∑_{k ≤ n} C(n, k) p^k (1 - p)^(n - k) = 1`. -/
theorem sum_binomPMF (n : ℕ) (p : ℝ) : ∑ k ∈ range (n + 1), binomPMF n p k = 1 := by
  have h := add_pow p (1 - p) n
  rw [add_sub_cancel, one_pow] at h
  rw [h]
  refine sum_congr rfl fun k _ => ?_
  unfold binomPMF
  ring

/-- `u / (u + v)` lies in `(0, 1)` for positive `u`, `v`. -/
theorem div_add_mem_Ioo {u v : ℝ} (hu : 0 < u) (hv : 0 < v) : u / (u + v) ∈ Set.Ioo (0 : ℝ) 1 :=
  ⟨div_pos hu (add_pos hu hv), (div_lt_one (add_pos hu hv)).2 (by linarith)⟩

/-- **The blocked binomial update of the latent cells, normalized.** Fix the observed margins
`a = W + X` and `b = Y + Z`, positive prior shapes and `se`, `sp`, `π` in `(0, 1)`. The predictive
values `ppv = se π / (se π + (1 - sp)(1 - π))` and `npv = sp (1 - π) / (sp (1 - π) + (1 - se) π)`
lie in `(0, 1)`; the joint density on the latent support `W ≤ a`, `Z ≤ b` (with `X = a - W`,
`Y = b - Z`) is a positive constant times `Bin(a, ppv) {W} · Bin(b, npv) {Z}`; its total mass
over the support is positive; and the normalized conditional law of `(W, Z)` is
`Bin(a, ppv) ⊗ Bin(b, npv)`. -/
theorem gibbs_WZ_conditional {α β γ δ εa εb se sp π : ℝ} (hα : 0 < α) (hβ : 0 < β)
    (hγ : 0 < γ) (hδ : 0 < δ) (ha : 0 < εa) (hb : 0 < εb) (hse : se ∈ Set.Ioo (0 : ℝ) 1)
    (hsp : sp ∈ Set.Ioo (0 : ℝ) 1) (hπ : π ∈ Set.Ioo (0 : ℝ) 1) (a b : ℕ) :
    let ppv := se * π / (se * π + (1 - sp) * (1 - π))
    let npv := sp * (1 - π) / (sp * (1 - π) + (1 - se) * π)
    let f : ℕ → ℕ → ℝ := fun W Z => gibbsJoint α β γ δ εa εb se sp π W (a - W) (b - Z) Z
    ppv ∈ Set.Ioo (0 : ℝ) 1 ∧ npv ∈ Set.Ioo (0 : ℝ) 1 ∧
      0 < ∑ W ∈ range (a + 1), ∑ Z ∈ range (b + 1), f W Z ∧
      ∀ W ≤ a, ∀ Z ≤ b,
        f W Z / (∑ W' ∈ range (a + 1), ∑ Z' ∈ range (b + 1), f W' Z') =
          binomPMF a ppv W * binomPMF b npv Z := by
  intro ppv npv f
  have hse1 : 0 < 1 - se := sub_pos.2 hse.2
  have hsp1 : 0 < 1 - sp := sub_pos.2 hsp.2
  have hπ1 : 0 < 1 - π := sub_pos.2 hπ.2
  have hu1 : 0 < se * π := mul_pos hse.1 hπ.1
  have hu2 : 0 < (1 - sp) * (1 - π) := mul_pos hsp1 hπ1
  have hv1 : 0 < sp * (1 - π) := mul_pos hsp.1 hπ1
  have hv2 : 0 < (1 - se) * π := mul_pos hse1 hπ.1
  have hP := betaPDFReal_pos hse.1 hse.2 hα hβ
  have hQ := betaPDFReal_pos hsp.1 hsp.2 hγ hδ
  have hR := betaPDFReal_pos hπ.1 hπ.2 ha hb
  have hm := multinomCoeff_pos a 0 b 0
  set C := betaPDFReal α β se * betaPDFReal γ δ sp * betaPDFReal εa εb π *
    multinomCoeff a 0 b 0 * (se * π + (1 - sp) * (1 - π)) ^ a *
    (sp * (1 - π) + (1 - se) * π) ^ b with hC
  have hCpos : 0 < C := by positivity
  have key : ∀ W ≤ a, ∀ Z ≤ b, f W Z = C * (binomPMF a ppv W * binomPMF b npv Z) := by
    intro W hW Z hZ
    have h1 := choose_mul_pow_eq_binomPMF hW (add_pos hu1 hu2).ne'
    have h2 := choose_mul_pow_eq_binomPMF hZ (add_pos hv1 hv2).ne'
    have hmc : multinomCoeff W (a - W) (b - Z) Z =
        multinomCoeff a 0 b 0 * b.choose Z * a.choose W := by
      rw [multinomCoeff_sub_left hW, multinomCoeff_sub_right a 0 hZ]
    simp only [f, gibbsJoint, latentLik, hmc, hC]
    linear_combination (betaPDFReal α β se * betaPDFReal γ δ sp * betaPDFReal εa εb π *
        multinomCoeff a 0 b 0 * ((b.choose Z : ℝ) * (sp * (1 - π)) ^ Z *
          ((1 - se) * π) ^ (b - Z))) * h1 +
      (betaPDFReal α β se * betaPDFReal γ δ sp * betaPDFReal εa εb π *
        multinomCoeff a 0 b 0 * (se * π + (1 - sp) * (1 - π)) ^ a *
          binomPMF a (se * π / (se * π + (1 - sp) * (1 - π))) W) * h2
  have hsum : ∑ W ∈ range (a + 1), ∑ Z ∈ range (b + 1), f W Z = C := by
    rw [sum_congr rfl fun W hW => sum_congr rfl fun Z hZ =>
      key W (Nat.lt_succ_iff.1 (mem_range.1 hW)) Z (Nat.lt_succ_iff.1 (mem_range.1 hZ))]
    calc ∑ W ∈ range (a + 1), ∑ Z ∈ range (b + 1), C * (binomPMF a ppv W * binomPMF b npv Z)
        = C * ((∑ W ∈ range (a + 1), binomPMF a ppv W) *
            ∑ Z ∈ range (b + 1), binomPMF b npv Z) := by
          rw [sum_mul_sum, mul_sum]
          exact sum_congr rfl fun _ _ => by rw [mul_sum]
      _ = C := by rw [sum_binomPMF, sum_binomPMF, mul_one, mul_one]
  refine ⟨div_add_mem_Ioo hu1 hu2, div_add_mem_Ioo hv1 hv2, hsum ▸ hCpos, fun W hW Z hZ => ?_⟩
  rw [hsum, key W hW Z hZ, mul_div_cancel_left₀ _ hCpos.ne']

end Gibbs

section RecordLevel

open MeasureTheory ProbabilityTheory

variable {Ω : Type*} [MeasurableSpace Ω]

/-- Record level and summary level reclassification agree in expectation (Fox, MacLehose and
Lash 2021, Chapter 9, Tables 9.5 to 9.8). Each of the `a` records classified as exposed is
reclassified as truly exposed by a Bernoulli draw `E₁ i ~ Bin(1, ppv)`, and each of the `b`
records classified as unexposed by a Bernoulli draw `E₀ j ~ Bin(1, 1 - npv)`. The expected number
of truly exposed records is `a ppv + b (1 - npv)`, the summary level count of Chapter 8 (the
predictive value correction `A = a PPV + b (1 - NPV)`). No independence between records is
needed: this is linearity of expectation. -/
theorem integral_reclassified_count (P : Measure Ω) [IsProbabilityMeasure P] {a b : ℕ}
    (ppv npv : unitInterval) (E₁ : Fin a → Ω → ℝ) (E₀ : Fin b → Ω → ℝ)
    (h₁ : ∀ i, HasLaw (E₁ i) (Bin(ℝ, 1, ppv)) P)
    (h₀ : ∀ j, HasLaw (E₀ j) (Bin(ℝ, 1, unitInterval.symm npv)) P) :
    ∫ ω, (∑ i, E₁ i ω + ∑ j, E₀ j ω) ∂P = a * (ppv : ℝ) + b * (1 - (npv : ℝ)) := by
  have hi₁ : ∀ i, Integrable (E₁ i) P := fun i => (h₁ i).integrable (integrable_map_cast_binomial _)
  have hi₀ : ∀ j, Integrable (E₀ j) P := fun j => (h₀ j).integrable (integrable_map_cast_binomial _)
  rw [integral_add (integrable_finsetSum _ fun i _ => hi₁ i)
      (integrable_finsetSum _ fun j _ => hi₀ j),
    integral_finsetSum _ fun i _ => hi₁ i, integral_finsetSum _ fun j _ => hi₀ j]
  simp only [fun i => integral_of_hasLaw_binomial (h₁ i),
    fun j => integral_of_hasLaw_binomial (h₀ j),
    unitInterval.coe_symm_eq, Nat.cast_one, mul_one, sum_const, card_univ, Fintype.card_fin,
    nsmul_eq_mul]

/-- The summary level counterpart: drawing the truly exposed among the `a` classified exposed as
one `Bin(a, ppv)` count and among the `b` classified unexposed as one `Bin(b, 1 - npv)` count
gives the same expected total `a ppv + b (1 - npv)`. -/
theorem integral_reclassified_binomial (P : Measure Ω) {a b : ℕ} (ppv npv : unitInterval)
    (T₁ T₀ : Ω → ℝ) (h₁ : HasLaw T₁ (Bin(ℝ, a, ppv)) P)
    (h₀ : HasLaw T₀ (Bin(ℝ, b, unitInterval.symm npv)) P) :
    ∫ ω, (T₁ ω + T₀ ω) ∂P = a * (ppv : ℝ) + b * (1 - (npv : ℝ)) := by
  rw [integral_add (h₁.integrable (integrable_map_cast_binomial _))
      (h₀.integrable (integrable_map_cast_binomial _)),
    integral_of_hasLaw_binomial h₁, integral_of_hasLaw_binomial h₀, unitInterval.coe_symm_eq]
  ring

end RecordLevel

section Examples

/-- Chapter 11, depression screening example (Equations 11.2 to 11.4): `x = 372` of `N = 774`
screen positive, so `p̂ = 372/774 ≈ 0.48`. With `Se = 0.95` and `Sp = 0.70` the true prevalence
with apparent prevalence `p̂` is `π̂ = (p̂ - 0.3)/0.65 ≈ 0.28`, the printed estimate. (The claim
that `π̂` maximizes the likelihood is not proved here.) -/
theorem depression_example :
    (372 : ℕ) + 402 = 774 ∧ (0.48 : ℝ) < 372 / 774 ∧ (372 / 774 : ℝ) < 0.49 ∧
      Bias.observedPrevalence 0.95 0.70 ((372 / 774 - 0.3) / 0.65) = 372 / 774 ∧
      (0.27 : ℝ) < (372 / 774 - 0.3) / 0.65 ∧ (372 / 774 - 0.3) / 0.65 < (0.285 : ℝ) := by
  rw [Bias.observedPrevalence_eq]
  norm_num

/-- Chapter 9, Tables 9.7 and 9.8: one record level reclassification of the smoking and breast
cancer data. The retained proportions are `163/215 ≈ 75.81%`, `1389/1449 ≈ 95.86%`,
`481/668 ≈ 72.01%`, `4084/4296 ≈ 95.07%`; the reclassified table is `223 = 163 + 60`,
`1441 = 1389 + 52`, `693 = 481 + 212`, `4271 = 4084 + 187`; the observed odds ratio
`215 · 4296 / (1449 · 668) ≈ 0.9542` and the reclassified one `223 · 4271 / (1441 · 693) ≈ 0.9538`.
The expected number of truly exposed cases under the predictive values of Table 9.5 is
`215 · 0.721 + 1449 · 0.044 ≈ 218.8` (`integral_reclassified_binomial`), of which `223` is one
random realization. -/
theorem recordLevel_example :
    (0.7581 : ℝ) < 163 / 215 ∧ (163 / 215 : ℝ) < 0.7582 ∧
      (0.9585 : ℝ) < 1389 / 1449 ∧ (1389 / 1449 : ℝ) < 0.9586 ∧
      (0.7200 : ℝ) < 481 / 668 ∧ (481 / 668 : ℝ) < 0.7201 ∧
      (0.9506 : ℝ) < 4084 / 4296 ∧ (4084 / 4296 : ℝ) < 0.9507 ∧
      163 + 60 = 223 ∧ 1389 + 52 = 1441 ∧ 481 + 212 = 693 ∧ 4084 + 187 = 4271 ∧
      (0.9542 : ℝ) < 215 * 4296 / (1449 * 668) ∧ (215 * 4296 / (1449 * 668) : ℝ) < 0.9543 ∧
      (0.9537 : ℝ) < 223 * 4271 / (1441 * 693) ∧ (223 * 4271 / (1441 * 693) : ℝ) < 0.9538 ∧
      (215 : ℝ) * 0.721 + 1449 * (1 - 0.956) = 218.771 := by
  norm_num

/-- Chapter 11 appendix: the pooled nondifferential updates of the first Gibbs iteration. With
the initial latent cells `W₁ = 200`, `X₁ = 15`, `Y₁ = 449`, `Z₁ = 1000` (cases) and `W₀ = 600`,
`X₀ = 68`, `Y₀ = 296`, `Z₀ = 4000` (controls), the margins match the observed table
(`a = 215`, `b = 1449`, `c = 668`, `d = 4296`), and the conditionals of `nondifferential_se`,
`nondifferential_sp` and `gibbsJoint_prevalence` are `Beta(50.6 + 800, 14.3 + 745)`,
`Beta(70 + 5000, 1 + 83)` and `Beta(1 + 649, 1 + 1015)`, as printed. With the sampled
`se = 0.362`, `sp = 0.990`, `π₁ = 0.395` the predictive values of `gibbsJoint_W` and
`gibbsJoint_Z` are `ppv₁ ≈ 0.959` and `npv₁ ≈ 0.704`, as printed.

The printed draw `se = 0.362` does not follow from the printed inputs. The conditional
`Beta(850.6, 759.3)` has mean `850.6 / 1609.9 ≈ 0.528` and variance
`850.6 · 759.3 / (1609.9² · 1610.9)`, and `0.362` lies more than 13 standard deviations below the
mean (last conjunct). The printed initial cells of the cases also imply a sensitivity
`200 / 649 ≈ 0.31`, not the stated initial value `0.78`. The arithmetic of the predictive values
from the printed draws is correct. -/
theorem gibbs_example :
    200 + 15 = 215 ∧ 449 + 1000 = 1449 ∧ 600 + 68 = 668 ∧ 296 + 4000 = 4296 ∧
      200 + 600 = 800 ∧ 449 + 296 = 745 ∧ 1000 + 4000 = 5000 ∧ 15 + 68 = 83 ∧
      200 + 449 = 649 ∧ 15 + 1000 = 1015 ∧
      (0.959 : ℝ) < 0.362 * 0.395 / (0.362 * 0.395 + (1 - 0.990) * (1 - 0.395)) ∧
      (0.362 * 0.395 / (0.362 * 0.395 + (1 - 0.990) * (1 - 0.395)) : ℝ) < 0.9595 ∧
      (0.7035 : ℝ) < 0.990 * (1 - 0.395) / (0.990 * (1 - 0.395) + (1 - 0.362) * 0.395) ∧
      (0.990 * (1 - 0.395) / (0.990 * (1 - 0.395) + (1 - 0.362) * 0.395) : ℝ) < 0.7045 ∧
      (0.308 : ℝ) < 200 / 649 ∧ (200 / 649 : ℝ) < 0.309 ∧
      (0.528 : ℝ) < 850.6 / (850.6 + 759.3) ∧ (850.6 / (850.6 + 759.3) : ℝ) < 0.529 ∧
      13 ^ 2 * (850.6 * 759.3 / ((850.6 + 759.3) ^ 2 * (850.6 + 759.3 + 1))) <
        (850.6 / (850.6 + 759.3) - 0.362 : ℝ) ^ 2 := by
  norm_num

end Examples

end Bayesian

end BiasAnalysis

end CausalInference
