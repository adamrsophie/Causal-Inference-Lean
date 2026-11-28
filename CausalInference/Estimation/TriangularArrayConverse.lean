/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.Estimation.TriangularArrayLimit

/-!
# The Feller converse of the Lindeberg theorem

Let row `n` of a triangular array be independent, centered, square integrable real random
variables `X n 0, …, X n (k n - 1)` with `∑_i E[X_{n,i}²] → v`. If the array is **uniformly
asymptotically negligible**, `max_i E[X_{n,i}²] → 0`, and the row sums converge in distribution to
`N(0, v)`, then the Lindeberg condition holds: `∑_i E[X_{n,i}² 1{ε < |X_{n,i}|}] → 0` for every
`ε > 0`. With the Lindeberg theorem `TriangularArray.tendstoInDistribution_sum` this gives the
equivalence of the central limit theorem and the Lindeberg condition for negligible arrays.

The proof compares characteristic functions. Write `a_{n,i} = φ_{n,i}(t) - 1`. Centering gives
`|a_{n,i}| ≤ 4 t² E[X_{n,i}²]`, so `max_i |a_{n,i}| → 0` and `∑_i |a_{n,i}|` stays bounded. Since
`Re a_{n,i} ≤ 0`, the numbers `φ_{n,i}(t)` and `exp(a_{n,i})` lie in the unit disc, and
`|∏_i φ_{n,i}(t) - exp(∑_i a_{n,i})| ≤ ∑_i |a_{n,i}|² → 0`. The central limit theorem gives
`∏_i φ_{n,i}(t) → exp(-t² v / 2)`; taking moduli and logarithms,
`∑_i E[1 - cos(t X_{n,i})] = -Re ∑_i a_{n,i} → t² v / 2`. Finally, for `t = 4 / ε`, the pointwise
inequality `6 x² 1{ε < |x|} ≤ 8 x² - ε² (1 - cos(t x))` (from `1 - cos y ≤ y² / 2` and
`1 - cos y ≤ 2 ≤ 2 x² / ε²` when `ε < |x|`) bounds the Lindeberg sum by a quantity tending to
`8 v - 8 v = 0`.

## Main definitions

* `CausalInference.TriangularArray.gaussianRowLaw`: the law of a row of independent centered
  Gaussian variables.
* `CausalInference.TriangularArray.singleVariances`: the variances `1, 0, …, 0` of row `n`.

## Main results

* `CausalInference.TriangularArray.norm_charFun_sub_one_le`: `|φ(t) - 1| ≤ 4 t² E[X²]`.
* `CausalInference.TriangularArray.tendsto_sum_one_sub_re_charFun`: for negligible rows whose
  characteristic function products converge to `exp(-t² v / 2)`,
  `∑_i (1 - Re φ_{n,i}(t)) → t² v / 2`.
* `CausalInference.TriangularArray.lindeberg_of_tendstoInDistribution_sum`: **the Feller
  converse**.
* `CausalInference.TriangularArray.tendstoInDistribution_sum_iff_lindeberg`: **the Lindeberg and
  Feller theorem**.
* `CausalInference.TriangularArray.gaussianRowLaw_tendstoInDistribution`: Gaussian rows with
  variances summing to `1` have row sums of law `N(0, 1)`.
* `CausalInference.TriangularArray.lindeberg_gaussianArray_uniform`: an instance, the array of
  `n + 1` independent `N(0, 1/(n+1))` variables per row.
* `CausalInference.TriangularArray.gaussianArray_single_not_lindeberg`: negligibility cannot be
  dropped. With one `N(0, 1)` variable and `n` zero variables per row, the row sums are exactly
  `N(0, 1)` but the Lindeberg condition fails.

## References

* J. W. Lindeberg (1922), *Eine neue Herleitung des Exponentialgesetzes in der
  Wahrscheinlichkeitsrechnung*, Mathematische Zeitschrift 15.
* W. Feller (1935), *Über den zentralen Grenzwertsatz der Wahrscheinlichkeitsrechnung*,
  Mathematische Zeitschrift 40.
* A. W. van der Vaart (1998), *Asymptotic Statistics*, chapter 2.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace CausalInference

namespace TriangularArray

/-! ### One variable -/

section OneLaw

variable {ν : Measure ℝ} [IsProbabilityMeasure ν]

/-- **The first order bound for a centered characteristic function.** For a centered law `ν` with
a finite second moment, `|φ(t) - 1| ≤ 4 t² E[X²]`. -/
theorem norm_charFun_sub_one_le (h2 : MemLp (fun x : ℝ ↦ x) 2 ν) (h0 : ∫ x, x ∂ν = 0) (t : ℝ) :
    ‖charFun ν t - 1‖ ≤ 4 * t ^ 2 * ∫ x, x ^ 2 ∂ν := by
  have he := charFun_sub_one_add_eq_integral h2 h0 t
  have hf2 : Integrable (fun x : ℝ ↦ x ^ 2) ν := h2.integrable_sq
  have hσ : 0 ≤ ∫ x, x ^ 2 ∂ν := integral_nonneg fun x ↦ sq_nonneg x
  have hb : ‖∫ x, taylorRemainder (t * x) ∂ν‖ ≤ 3 * t ^ 2 * ∫ x, x ^ 2 ∂ν := by
    rw [← integral_const_mul]
    refine norm_integral_le_of_norm_le (hf2.const_mul (3 * t ^ 2)) (ae_of_all _ fun x ↦ ?_)
    calc ‖taylorRemainder (t * x)‖ ≤ 3 * (t * x) ^ 2 := (norm_taylorRemainder_le (t * x)).2
      _ = 3 * t ^ 2 * x ^ 2 := by ring
  have e : charFun ν t - 1 =
      ∫ x, taylorRemainder (t * x) ∂ν - ((t ^ 2 / 2 * ∫ x, x ^ 2 ∂ν : ℝ) : ℂ) := by
    rw [← he]
    ring
  rw [e]
  refine (norm_sub_le _ _).trans ?_
  rw [Complex.norm_real, Real.norm_of_nonneg (by positivity)]
  nlinarith [mul_nonneg (sq_nonneg t) hσ]

/-- The real part of a characteristic function: `Re φ(t) = E[cos(t X)]`. -/
theorem re_charFun_eq_integral_cos (t : ℝ) :
    (charFun ν t).re = ∫ x, Real.cos (t * x) ∂ν := by
  have h1 : Integrable (fun x : ℝ ↦ Complex.exp (((t * x : ℝ) : ℂ) * Complex.I)) ν := by
    refine Integrable.of_bound (by fun_prop) 1 (ae_of_all _ fun x ↦ ?_)
    rw [Complex.norm_exp_ofReal_mul_I]
  have hcf : charFun ν t = ∫ x, Complex.exp (((t * x : ℝ) : ℂ) * Complex.I) ∂ν := by
    rw [charFun_apply_real]
    push_cast
    rfl
  have h := integral_re h1
  simp only [RCLike.re_to_complex, Complex.exp_ofReal_mul_I_re] at h
  rw [hcf, ← h]

/-- **The truncation inequality.** For a law `ν` with a finite second moment and `ε > 0`,
`6 E[X² 1{ε < |X|}] ≤ 8 E[X²] - ε² (1 - Re φ(4 / ε))`. It integrates the pointwise inequality
`6 x² 1{ε < |x|} ≤ 8 x² - ε² (1 - cos(4 x / ε))`. -/
theorem six_mul_setIntegral_sq_le (h2 : MemLp (fun x : ℝ ↦ x) 2 ν) {ε : ℝ} (hε : 0 < ε) :
    6 * ∫ x in {x | ε < |x|}, x ^ 2 ∂ν ≤
      8 * ∫ x, x ^ 2 ∂ν - ε ^ 2 * (1 - (charFun ν (4 / ε)).re) := by
  have hf2 : Integrable (fun x : ℝ ↦ x ^ 2) ν := h2.integrable_sq
  have hAm : MeasurableSet {x : ℝ | ε < |x|} := measurableSet_lt measurable_const (by fun_prop)
  have hcos : Integrable (fun x : ℝ ↦ Real.cos (4 / ε * x)) ν :=
    Integrable.of_bound (by fun_prop) 1 (ae_of_all _ fun x ↦ by
      rw [Real.norm_eq_abs]; exact Real.abs_cos_le_one _)
  have hind : Integrable ({x : ℝ | ε < |x|}.indicator fun x ↦ x ^ 2) ν :=
    (integrable_indicator_iff hAm).2 hf2.integrableOn
  have hR : Integrable (fun x : ℝ ↦ ε ^ 2 * (1 - Real.cos (4 / ε * x))) ν :=
    ((integrable_const 1).sub hcos).const_mul _
  have hRHS : 8 * ∫ x, x ^ 2 ∂ν - ε ^ 2 * (1 - ∫ x, Real.cos (4 / ε * x) ∂ν) =
      ∫ x, (8 * x ^ 2 - ε ^ 2 * (1 - Real.cos (4 / ε * x))) ∂ν := by
    rw [integral_sub (hf2.const_mul 8) hR, integral_const_mul, integral_const_mul,
      integral_sub (integrable_const 1) hcos, integral_const]
    simp
  have hLHS : 6 * ∫ x in {x | ε < |x|}, x ^ 2 ∂ν =
      ∫ x, 6 * {x : ℝ | ε < |x|}.indicator (fun x ↦ x ^ 2) x ∂ν := by
    rw [integral_const_mul, integral_indicator hAm]
  rw [re_charFun_eq_integral_cos, hLHS, hRHS]
  refine integral_mono (hind.const_mul 6) ((hf2.const_mul 8).sub hR) fun x ↦ ?_
  have hc1 := Real.neg_one_le_cos (4 / ε * x)
  have hc2 := Real.one_sub_sq_div_two_le_cos (x := 4 / ε * x)
  have hsq : x ^ 2 = |x| ^ 2 := (sq_abs x).symm
  have hε2 : 0 < ε ^ 2 := by positivity
  by_cases hx : ε < |x|
  · rw [Set.indicator_of_mem (show x ∈ {x : ℝ | ε < |x|} from hx)]
    have : ε ^ 2 ≤ x ^ 2 := by rw [hsq]; exact pow_le_pow_left₀ hε.le hx.le 2
    nlinarith
  · rw [Set.indicator_of_notMem (show x ∉ {x : ℝ | ε < |x|} from hx)]
    have hq : ε ^ 2 * ((4 / ε * x) ^ 2 / 2) = 8 * x ^ 2 := by
      field_simp
      ring
    nlinarith

end OneLaw

/-! ### Rows of laws -/

section Rows

variable {k : ℕ → ℕ} {ν : (n : ℕ) → Fin (k n) → Measure ℝ} [∀ n i, IsProbabilityMeasure (ν n i)]

/-- **Characteristic functions of negligible rows.** Let the laws `ν n i` be centered with finite
second moments, `∑_i E_{ν n i}[x²] → v`, and negligible: for every `η > 0`, eventually
`E_{ν n i}[x²] ≤ η` for all `i`. If `∏_i φ_{ν n i}(t) → exp(-t² v / 2)`, then
`∑_i (1 - Re φ_{ν n i}(t)) → t² v / 2`. -/
theorem tendsto_sum_one_sub_re_charFun (h2 : ∀ n i, MemLp (fun x : ℝ ↦ x) 2 (ν n i))
    (h0 : ∀ n i, ∫ x, x ∂ν n i = 0) {v : ℝ}
    (hv : Tendsto (fun n ↦ ∑ i, ∫ x, x ^ 2 ∂ν n i) atTop (𝓝 v))
    (hneg : ∀ η, 0 < η → ∀ᶠ n in atTop, ∀ i, ∫ x, x ^ 2 ∂ν n i ≤ η) (t : ℝ)
    (hprod : Tendsto (fun n ↦ ∏ i, charFun (ν n i) t) atTop
      (𝓝 (Complex.exp (-((t ^ 2 / 2 * v : ℝ) : ℂ))))) :
    Tendsto (fun n ↦ ∑ i, (1 - (charFun (ν n i) t).re)) atTop (𝓝 (t ^ 2 / 2 * v)) := by
  set σ2 : (n : ℕ) → Fin (k n) → ℝ := fun n i ↦ ∫ x, x ^ 2 ∂ν n i with hσ2
  set s : ℕ → ℝ := fun n ↦ ∑ i, σ2 n i with hs
  set a : (n : ℕ) → Fin (k n) → ℂ := fun n i ↦ charFun (ν n i) t - 1 with ha
  have hσ0 : ∀ n i, 0 ≤ σ2 n i := fun n i ↦ integral_nonneg fun x ↦ sq_nonneg x
  have han : ∀ n i, ‖a n i‖ ≤ 4 * t ^ 2 * σ2 n i := fun n i ↦
    norm_charFun_sub_one_le (h2 n i) (h0 n i) t
  have hφ : ∀ n i, ‖charFun (ν n i) t‖ ≤ 1 := fun n i ↦ norm_charFun_le_one t
  have hre : ∀ n i, (a n i).re ≤ 0 := fun n i ↦ by
    have h1 := Complex.re_le_norm (charFun (ν n i) t)
    simp only [ha, Complex.sub_re, Complex.one_re]
    linarith [hφ n i]
  have hea : ∀ n i, ‖Complex.exp (a n i)‖ ≤ 1 := fun n i ↦ by
    rw [Complex.norm_exp]
    exact Real.exp_le_one_iff.2 (hre n i)
  -- the termwise comparison with `exp (a n i)`
  have hsum : Tendsto (fun n ↦ ∑ i, ‖charFun (ν n i) t - Complex.exp (a n i)‖) atTop
      (𝓝 0) := by
    refine tendsto_order.2 ⟨fun b hb ↦ Eventually.of_forall fun n ↦
      hb.trans_le (Finset.sum_nonneg fun _ _ ↦ norm_nonneg _), fun δ hδ ↦ ?_⟩
    set V := |v| + 1 with hV
    have hV0 : 0 < V := by positivity
    set η := min (1 / (4 * t ^ 2 + 1)) (δ / (2 * (16 * t ^ 4 + 1) * V)) with hηd
    have hη : 0 < η := lt_min (by positivity) (by positivity)
    have hsV : ∀ᶠ n in atTop, s n < V :=
      hv.eventually (gt_mem_nhds (by rw [hV]; linarith [le_abs_self v]))
    filter_upwards [hsV, hneg η hη] with n hsn hmax
    have hs0 : 0 ≤ s n := Finset.sum_nonneg fun i _ ↦ hσ0 n i
    have h4 : ∀ i, ‖a n i‖ ≤ 4 * t ^ 2 * η := fun i ↦
      (han n i).trans (mul_le_mul_of_nonneg_left (hmax i) (by positivity))
    have h1 : ∀ i, ‖a n i‖ ≤ 1 := fun i ↦ by
      have hm : η ≤ 1 / (4 * t ^ 2 + 1) := min_le_left _ _
      have : 4 * t ^ 2 * η ≤ 1 :=
        calc 4 * t ^ 2 * η ≤ 4 * t ^ 2 * (1 / (4 * t ^ 2 + 1)) :=
              mul_le_mul_of_nonneg_left hm (by positivity)
          _ ≤ 1 := by rw [mul_one_div, div_le_one (by positivity)]; linarith
      exact (h4 i).trans this
    have hpt : ∀ i, ‖charFun (ν n i) t - Complex.exp (a n i)‖ ≤ 16 * t ^ 4 * η * σ2 n i := by
      intro i
      have e : charFun (ν n i) t - Complex.exp (a n i) = -(Complex.exp (a n i) - 1 - a n i) := by
        simp only [ha]
        ring
      rw [e, norm_neg]
      refine (Complex.norm_exp_sub_one_sub_id_le (h1 i)).trans ?_
      have hn0 := norm_nonneg (a n i)
      calc ‖a n i‖ ^ 2 = ‖a n i‖ * ‖a n i‖ := sq _
        _ ≤ (4 * t ^ 2 * η) * (4 * t ^ 2 * σ2 n i) :=
            mul_le_mul (h4 i) (han n i) hn0 (by positivity)
        _ = 16 * t ^ 4 * η * σ2 n i := by ring
    have hm : η ≤ δ / (2 * (16 * t ^ 4 + 1) * V) := min_le_right _ _
    calc ∑ i, ‖charFun (ν n i) t - Complex.exp (a n i)‖ ≤ ∑ i, 16 * t ^ 4 * η * σ2 n i :=
          Finset.sum_le_sum fun i _ ↦ hpt i
      _ = 16 * t ^ 4 * η * s n := by rw [← Finset.mul_sum]
      _ ≤ (16 * t ^ 4 + 1) * η * V :=
          mul_le_mul (mul_le_mul_of_nonneg_right (by linarith) hη.le) hsn.le hs0
            (by positivity)
      _ ≤ (16 * t ^ 4 + 1) * (δ / (2 * (16 * t ^ 4 + 1) * V)) * V := by gcongr
      _ = δ / 2 := by field_simp
      _ < δ := by linarith
  have hdiff : Tendsto (fun n ↦ ∏ i, charFun (ν n i) t - Complex.exp (∑ i, a n i)) atTop
      (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    refine squeeze_zero (fun _ ↦ norm_nonneg _) (fun n ↦ ?_) hsum
    rw [Complex.exp_sum]
    exact norm_prod_sub_prod_le _ (fun i _ ↦ hφ n i) (fun i _ ↦ hea n i)
  have hexp : Tendsto (fun n ↦ Complex.exp (∑ i, a n i)) atTop
      (𝓝 (Complex.exp (-((t ^ 2 / 2 * v : ℝ) : ℂ)))) := by
    simpa using hprod.sub hdiff
  have hnorm := hexp.norm
  simp only [Complex.norm_exp, Complex.re_sum, Complex.neg_re, Complex.ofReal_re] at hnorm
  have hlog := ((Real.continuousAt_log (Real.exp_pos _).ne').tendsto.comp hnorm).neg
  simp only [Function.comp_def, Real.log_exp, neg_neg] at hlog
  refine hlog.congr fun n ↦ ?_
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  simp [ha]

end Rows

/-! ### The Feller converse -/

section Converse

variable {Ω : ℕ → Type*} {mΩ : ∀ n, MeasurableSpace (Ω n)} {P : (n : ℕ) → Measure (Ω n)}
  [∀ n, IsProbabilityMeasure (P n)] {k : ℕ → ℕ} {X : (n : ℕ) → Fin (k n) → Ω n → ℝ}

/-- **The Feller converse of the Lindeberg theorem.** For each `n` let `X n 0, …, X n (k n - 1)` be
independent real random variables on `(Ω n, P n)`, centered and square integrable, with
`∑_i E[X_{n,i}²] → v` and uniformly asymptotically negligible variances: for every `η > 0`,
eventually `E[X_{n,i}²] ≤ η` for all `i`. If the row sums `∑_i X_{n,i}` converge in distribution
to a variable `Y` with law `N(0, v)`, then the Lindeberg condition
`∑_i E[X_{n,i}² 1{ε < |X_{n,i}|}] → 0` holds for every `ε > 0`. -/
theorem lindeberg_of_tendstoInDistribution_sum (hind : ∀ n, iIndepFun (X n) (P n))
    (h2 : ∀ n i, MemLp (X n i) 2 (P n)) (h0 : ∀ n i, ∫ ω, X n i ω ∂P n = 0) {v : ℝ}
    (hv : Tendsto (fun n ↦ ∑ i, ∫ ω, X n i ω ^ 2 ∂P n) atTop (𝓝 v))
    (hneg : ∀ η, 0 < η → ∀ᶠ n in atTop, ∀ i, ∫ ω, X n i ω ^ 2 ∂P n ≤ η)
    {Ω' : Type*} {mΩ' : MeasurableSpace Ω'} {P' : Measure Ω'} [IsProbabilityMeasure P']
    {Y : Ω' → ℝ} (hY : HasLaw Y (gaussianReal 0 v.toNNReal) P')
    (hclt : TendstoInDistribution (fun n ω ↦ ∑ i, X n i ω) atTop Y P P') :
    ∀ ε, 0 < ε → Tendsto (fun n ↦ ∑ i,
      ∫ ω, {x : ℝ | ε < |x|}.indicator (fun x ↦ x ^ 2) (X n i ω) ∂P n) atTop (𝓝 0) := by
  have hXm : ∀ n i, AEMeasurable (X n i) (P n) := fun n i ↦
    (h2 n i).aestronglyMeasurable.aemeasurable
  set ν : (n : ℕ) → Fin (k n) → Measure ℝ := fun n i ↦ (P n).map (X n i) with hν
  have hνp : ∀ n i, IsProbabilityMeasure (ν n i) := fun n i ↦ inferInstance
  have hm2 : ∀ n i, MemLp (fun x : ℝ ↦ x) 2 (ν n i) := fun n i ↦
    (memLp_map_measure_iff aestronglyMeasurable_id (hXm n i)).2 (h2 n i)
  have hint : ∀ n i {g : ℝ → ℝ}, Measurable g → ∫ x, g x ∂ν n i = ∫ ω, g (X n i ω) ∂P n :=
    fun n i g hg ↦ integral_map (hXm n i) hg.aestronglyMeasurable
  have hAm : ∀ ε : ℝ, MeasurableSet {x : ℝ | ε < |x|} := fun ε ↦
    measurableSet_lt measurable_const (by fun_prop)
  have h0' : ∀ n i, ∫ x, x ∂ν n i = 0 := fun n i ↦ by
    rw [hint n i (g := fun x ↦ x) measurable_id]
    exact h0 n i
  have hsq : ∀ n i, ∫ x, x ^ 2 ∂ν n i = ∫ ω, X n i ω ^ 2 ∂P n := fun n i ↦
    hint n i (by fun_prop)
  have hv' : Tendsto (fun n ↦ ∑ i, ∫ x, x ^ 2 ∂ν n i) atTop (𝓝 v) :=
    hv.congr fun n ↦ Finset.sum_congr rfl fun i _ ↦ (hsq n i).symm
  have hneg' : ∀ η, 0 < η → ∀ᶠ n in atTop, ∀ i, ∫ x, x ^ 2 ∂ν n i ≤ η := fun η hη ↦
    (hneg η hη).mono fun n hn i ↦ (hsq n i).trans_le (hn i)
  have hv0 : 0 ≤ v := ge_of_tendsto' hv fun n ↦ Finset.sum_nonneg fun i _ ↦
    integral_nonneg fun ω ↦ sq_nonneg _
  have hprod : ∀ t : ℝ, Tendsto (fun n ↦ ∏ i, charFun (ν n i) t) atTop
      (𝓝 (Complex.exp (-((t ^ 2 / 2 * v : ℝ) : ℂ)))) := by
    intro t
    have h := hclt.tendsto_charFun t
    rw [hY.map_eq, charFun_gaussianReal] at h
    have heq : Complex.exp (t * ((0 : ℝ) : ℂ) * Complex.I - ((v.toNNReal : ℝ) : ℂ) * t ^ 2 / 2) =
        Complex.exp (-((t ^ 2 / 2 * v : ℝ) : ℂ)) := by
      congr 1
      rw [Real.coe_toNNReal v hv0]
      push_cast
      ring
    rw [heq] at h
    refine h.congr fun n ↦ ?_
    rw [(hind n).charFun_map_fun_sum_eq_prod (hXm n), Finset.prod_apply]
  intro ε hε
  have hcos := tendsto_sum_one_sub_re_charFun hm2 h0' hv' hneg' (4 / ε) (hprod (4 / ε))
  have hlim : Tendsto (fun n ↦ (8 * ∑ i, ∫ x, x ^ 2 ∂ν n i -
      ε ^ 2 * ∑ i, (1 - (charFun (ν n i) (4 / ε)).re)) / 6) atTop (𝓝 0) := by
    have h := ((hv'.const_mul 8).sub (hcos.const_mul (ε ^ 2))).div_const 6
    have hz : (8 * v - ε ^ 2 * ((4 / ε) ^ 2 / 2 * v)) / 6 = 0 := by
      field_simp
      ring
    rwa [hz] at h
  have hL0 : ∀ n i, 0 ≤ ∫ x in {x | ε < |x|}, x ^ 2 ∂ν n i := fun n i ↦
    setIntegral_nonneg (hAm ε) fun x _ ↦ sq_nonneg x
  have hlaw : Tendsto (fun n ↦ ∑ i, ∫ x in {x | ε < |x|}, x ^ 2 ∂ν n i) atTop (𝓝 0) := by
    refine squeeze_zero (fun n ↦ Finset.sum_nonneg fun i _ ↦ hL0 n i) (fun n ↦ ?_) hlim
    rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 6), Finset.mul_sum, Finset.mul_sum, Finset.sum_mul,
      ← Finset.sum_sub_distrib]
    refine Finset.sum_le_sum fun i _ ↦ ?_
    have := six_mul_setIntegral_sq_le (hm2 n i) hε
    linarith
  refine hlaw.congr fun n ↦ Finset.sum_congr rfl fun i _ ↦ ?_
  rw [← integral_indicator (hAm ε),
    hint n i ((by fun_prop : Measurable fun x : ℝ ↦ x ^ 2).indicator (hAm ε))]

/-- **The Lindeberg and Feller theorem.** For a triangular array of row independent, centered,
square integrable real random variables with `∑_i E[X_{n,i}²] → v` and uniformly asymptotically
negligible variances, the row sums converge in distribution to `N(0, v)` if and only if the
Lindeberg condition holds. -/
theorem tendstoInDistribution_sum_iff_lindeberg (hind : ∀ n, iIndepFun (X n) (P n))
    (h2 : ∀ n i, MemLp (X n i) 2 (P n)) (h0 : ∀ n i, ∫ ω, X n i ω ∂P n = 0) {v : ℝ}
    (hv : Tendsto (fun n ↦ ∑ i, ∫ ω, X n i ω ^ 2 ∂P n) atTop (𝓝 v))
    (hneg : ∀ η, 0 < η → ∀ᶠ n in atTop, ∀ i, ∫ ω, X n i ω ^ 2 ∂P n ≤ η)
    {Ω' : Type*} {mΩ' : MeasurableSpace Ω'} {P' : Measure Ω'} [IsProbabilityMeasure P']
    {Y : Ω' → ℝ} (hY : HasLaw Y (gaussianReal 0 v.toNNReal) P') :
    TendstoInDistribution (fun n ω ↦ ∑ i, X n i ω) atTop Y P P' ↔
      ∀ ε, 0 < ε → Tendsto (fun n ↦ ∑ i,
        ∫ ω, {x : ℝ | ε < |x|}.indicator (fun x ↦ x ^ 2) (X n i ω) ∂P n) atTop (𝓝 0) :=
  ⟨lindeberg_of_tendstoInDistribution_sum hind h2 h0 hv hneg hY,
    fun hL ↦ tendstoInDistribution_sum hind h2 h0 hv hL hY⟩

end Converse

/-! ### Gaussian rows: an instance and a counterexample -/

section Gaussian

/-- The law of a row of independent centered Gaussian variables with variances `w 0, …, w (m - 1)`,
as a product measure on `ℝ^m`. -/
noncomputable def gaussianRowLaw {m : ℕ} (w : Fin m → ℝ≥0) : Measure (Fin m → ℝ) :=
  Measure.pi fun i ↦ gaussianReal 0 (w i)

instance isProbabilityMeasure_gaussianRowLaw {m : ℕ} (w : Fin m → ℝ≥0) :
    IsProbabilityMeasure (gaussianRowLaw w) := by
  unfold gaussianRowLaw
  infer_instance

/-- The second moment of a centered Gaussian law is its variance. -/
theorem integral_sq_gaussianReal_zero (v : ℝ≥0) : ∫ x, x ^ 2 ∂gaussianReal 0 v = v := by
  rw [← variance_of_integral_eq_zero aemeasurable_id' integral_id_gaussianReal,
    variance_fun_id_gaussianReal]

theorem hasLaw_eval_gaussianRowLaw {m : ℕ} (w : Fin m → ℝ≥0) (i : Fin m) :
    HasLaw (fun x : Fin m → ℝ ↦ x i) (gaussianReal 0 (w i)) (gaussianRowLaw w) :=
  ⟨(measurable_pi_apply i).aemeasurable, (measurePreserving_eval _ i).map_eq⟩

/-- **The coordinates of a Gaussian row** are independent, square integrable, centered, with
second moments `w i`. -/
theorem gaussianRowLaw_moments {m : ℕ} (w : Fin m → ℝ≥0) :
    iIndepFun (fun (i : Fin m) (x : Fin m → ℝ) ↦ x i) (gaussianRowLaw w) ∧
      (∀ i, MemLp (fun x : Fin m → ℝ ↦ x i) 2 (gaussianRowLaw w)) ∧
      (∀ i, ∫ x, x i ∂gaussianRowLaw w = 0) ∧
      ∀ i, ∫ x, x i ^ 2 ∂gaussianRowLaw w = w i := by
  refine ⟨iIndepFun_pi (X := fun _ x ↦ x) fun _ ↦ aemeasurable_id', fun i ↦
    (hasLaw_eval_gaussianRowLaw w i).memLp (memLp_id_gaussianReal' 2 (by simp)), fun i ↦ ?_,
    fun i ↦ ?_⟩
  · rw [(hasLaw_eval_gaussianRowLaw w i).integral_eq, integral_id_gaussianReal]
  · have h := (hasLaw_eval_gaussianRowLaw w i).integral_comp (f := fun x : ℝ ↦ x ^ 2)
      (by fun_prop)
    simp only [Function.comp_def] at h
    rw [h, integral_sq_gaussianReal_zero]

/-- **Gaussian rows with unit total variance.** If `∑_i w n i = 1` for every `n`, the row sums of
the array of independent `N(0, w n i)` variables have law `N(0, 1)` for every `n`, so they
converge in distribution to every `Y` with law `N(0, 1)`. -/
theorem gaussianRowLaw_tendstoInDistribution {k : ℕ → ℕ} (w : (n : ℕ) → Fin (k n) → ℝ≥0)
    (hw : ∀ n, ∑ i, (w n i : ℝ) = 1) {Ω' : Type*} {mΩ' : MeasurableSpace Ω'} {P' : Measure Ω'}
    [IsProbabilityMeasure P'] {Y : Ω' → ℝ} (hY : HasLaw Y (gaussianReal 0 1) P') :
    TendstoInDistribution (fun (n : ℕ) (x : Fin (k n) → ℝ) ↦ ∑ i, x i) atTop Y
      (fun n ↦ gaussianRowLaw (w n)) P' := by
  refine TendstoInDistribution.of_tendsto_charFun (fun n ↦ by fun_prop) hY.aemeasurable
    fun t ↦ tendsto_const_nhds.congr fun n ↦ ?_
  rw [hY.map_eq, gaussianRowLaw, charFun_map_sum_pi_eq_prod, Finset.prod_apply]
  simp only [charFun_gaussianReal, ← Complex.exp_sum]
  congr 1
  have h : ∑ i, ((w n i : ℝ) : ℂ) = 1 := by exact_mod_cast hw n
  simp only [Complex.ofReal_zero, mul_zero, zero_mul, zero_sub, Finset.sum_neg_distrib,
    ← Finset.sum_div, ← Finset.sum_mul, h, NNReal.coe_one, Complex.ofReal_one]

/-- **An instance of the Feller converse.** For the array whose row `n` consists of `n + 1`
independent `N(0, 1/(n+1))` variables, the Lindeberg condition holds. It follows from the Feller
converse: the variances are negligible, they sum to `1`, and the row sums have law `N(0, 1)`. -/
theorem lindeberg_gaussianArray_uniform :
    ∀ ε, 0 < ε → Tendsto (fun n : ℕ ↦ ∑ i : Fin (n + 1),
      ∫ x, {y : ℝ | ε < |y|}.indicator (fun y ↦ y ^ 2) (x i)
        ∂gaussianRowLaw (fun _ ↦ ((n : ℝ≥0) + 1)⁻¹)) atTop (𝓝 0) := by
  set w : (n : ℕ) → Fin (n + 1) → ℝ≥0 := fun n _ ↦ ((n : ℝ≥0) + 1)⁻¹ with hwd
  have hm := fun n ↦ gaussianRowLaw_moments (w n)
  have hwr : ∀ n, ((((n : ℝ≥0) + 1)⁻¹ : ℝ≥0) : ℝ) = 1 / ((n : ℝ) + 1) := fun n ↦ by
    push_cast
    rw [one_div]
  have hw : ∀ n, ∑ i, (w n i : ℝ) = 1 := fun n ↦ by
    simp only [hwd, hwr, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    push_cast
    field_simp
  have hY : HasLaw (fun x : ℝ ↦ x) (gaussianReal 0 (1 : ℝ).toNNReal) (gaussianReal 0 1) := by
    rw [Real.toNNReal_one]
    exact ⟨aemeasurable_id', Measure.map_id⟩
  refine lindeberg_of_tendstoInDistribution_sum (fun n ↦ (hm n).1) (fun n ↦ (hm n).2.1)
    (fun n ↦ (hm n).2.2.1) (v := 1) ?_ ?_ hY ?_
  · exact tendsto_const_nhds.congr fun n ↦
      ((Finset.sum_congr rfl fun i _ ↦ (hm n).2.2.2 i).trans (hw n)).symm
  · intro η hη
    filter_upwards [(tendsto_one_div_add_atTop_nhds_zero_nat).eventually (gt_mem_nhds hη)]
      with n hn i
    rw [(hm n).2.2.2, hwd, hwr]
    exact hn.le
  · rw [Real.toNNReal_one] at hY
    exact gaussianRowLaw_tendstoInDistribution w hw hY

/-- The variances of the array with one `N(0, 1)` variable and `n` zero variables in row `n`. -/
def singleVariances (n : ℕ) (i : Fin (n + 1)) : ℝ≥0 := if i = 0 then 1 else 0

/-- **Negligibility cannot be dropped from the Feller converse.** Let row `n` consist of one
`N(0, 1)` variable and `n` variables equal to `0` almost surely (law `N(0, 0)`), all independent.
The variables are centered and square integrable, the row variances sum to `1`, and the row sums
have law `N(0, 1)`, so they converge in distribution to `N(0, 1)`. The variances are not
negligible, and the Lindeberg condition fails: for `ε = 1/2` the Lindeberg sums are at least
`3/4`. -/
theorem gaussianArray_single_not_lindeberg :
    (∀ n, iIndepFun (fun (i : Fin (n + 1)) (x : Fin (n + 1) → ℝ) ↦ x i)
      (gaussianRowLaw (singleVariances n))) ∧
    (∀ n i, MemLp (fun x : Fin (n + 1) → ℝ ↦ x i) 2 (gaussianRowLaw (singleVariances n))) ∧
    (∀ n i, ∫ x, x i ∂gaussianRowLaw (singleVariances n) = 0) ∧
    (∀ n, ∑ i, ∫ x, x i ^ 2 ∂gaussianRowLaw (singleVariances n) = 1) ∧
    TendstoInDistribution (fun (n : ℕ) (x : Fin (n + 1) → ℝ) ↦ ∑ i, x i) atTop (fun y : ℝ ↦ y)
      (fun n ↦ gaussianRowLaw (singleVariances n)) (gaussianReal 0 1) ∧
    ¬ (∀ η, 0 < η → ∀ᶠ n in atTop, ∀ i,
      ∫ x, x i ^ 2 ∂gaussianRowLaw (singleVariances n) ≤ η) ∧
    ¬ (∀ ε, 0 < ε → Tendsto (fun n : ℕ ↦ ∑ i : Fin (n + 1),
      ∫ x, {y : ℝ | ε < |y|}.indicator (fun y ↦ y ^ 2) (x i)
        ∂gaussianRowLaw (singleVariances n)) atTop (𝓝 0)) := by
  have hm := fun n ↦ gaussianRowLaw_moments (singleVariances n)
  have hw : ∀ n, ∑ i, (singleVariances n i : ℝ) = 1 := fun n ↦ by
    rw [Fintype.sum_eq_single 0 fun i hi ↦ by simp [singleVariances, hi]]
    simp [singleVariances]
  have h00 : ∀ n, ∫ x, x 0 ^ 2 ∂gaussianRowLaw (singleVariances n) = 1 := fun n ↦ by
    rw [(hm n).2.2.2]
    simp [singleVariances]
  refine ⟨fun n ↦ (hm n).1, fun n ↦ (hm n).2.1, fun n ↦ (hm n).2.2.1, fun n ↦ ?_,
    gaussianRowLaw_tendstoInDistribution singleVariances hw ⟨aemeasurable_id', Measure.map_id⟩,
    fun h ↦ ?_, fun h ↦ ?_⟩
  · exact (Finset.sum_congr rfl fun i _ ↦ (hm n).2.2.2 i).trans (hw n)
  · obtain ⟨n, hn⟩ := (h (1 / 2) (by norm_num)).exists
    have := hn 0
    rw [h00] at this
    norm_num at this
  · obtain ⟨n, hn⟩ := ((h (1 / 2) (by norm_num)).eventually (gt_mem_nhds
      (by norm_num : (0 : ℝ) < 3 / 4))).exists
    have hAm : MeasurableSet {y : ℝ | 1 / 2 < |y|} :=
      measurableSet_lt measurable_const (by fun_prop)
    have hlaw := hasLaw_eval_gaussianRowLaw (singleVariances n) 0
    have hv0 : singleVariances n 0 = 1 := by simp [singleVariances]
    rw [hv0] at hlaw
    have hterm : ∫ x, {y : ℝ | 1 / 2 < |y|}.indicator (fun y ↦ y ^ 2) (x 0)
        ∂gaussianRowLaw (singleVariances n) = ∫ y in {y : ℝ | 1 / 2 < |y|}, y ^ 2
          ∂gaussianReal 0 1 := by
      have h := hlaw.integral_comp (f := {y : ℝ | 1 / 2 < |y|}.indicator (fun y ↦ y ^ 2))
        ((by fun_prop : Measurable fun y : ℝ ↦ y ^ 2).indicator hAm).aestronglyMeasurable
      simp only [Function.comp_def] at h
      rw [h, integral_indicator hAm]
    have hlow := integral_sq_le_add_setIntegral
      (ν := gaussianReal 0 1) (memLp_id_gaussianReal' 2 (by simp)) (1 / 2)
    rw [integral_sq_gaussianReal_zero, NNReal.coe_one] at hlow
    have hsingle := Finset.single_le_sum (f := fun i : Fin (n + 1) ↦
      ∫ x, {y : ℝ | 1 / 2 < |y|}.indicator (fun y ↦ y ^ 2) (x i)
        ∂gaussianRowLaw (singleVariances n))
      (fun i _ ↦ integral_nonneg fun x ↦ Set.indicator_nonneg (fun y _ ↦ sq_nonneg y) _)
      (Finset.mem_univ 0)
    simp only [hterm] at hsingle
    linarith

end Gaussian

end TriangularArray

end CausalInference
