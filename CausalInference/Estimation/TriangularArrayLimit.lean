/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import Mathlib.Probability.CentralLimitTheorem
public import Mathlib.MeasureTheory.Measure.LevyConvergence
public import Mathlib.Probability.Independence.CharacteristicFunction

/-!
# The Lindeberg central limit theorem for triangular arrays

Row `n` of a triangular array is a finite family `X n 0, …, X n (k n - 1)` of real random
variables on a probability space `(Ω n, P n)` that may change with `n`. The variables of a row are
independent and centered, with finite variances `σ²_{n,i}`, and they need not be identically
distributed. If the row variances sum to a limit, `∑_i σ²_{n,i} → v`, and the **Lindeberg
condition**

`∑_i E[X_{n,i}² 1{ε < |X_{n,i}|}] → 0` for every `ε > 0`

holds, then the row sums `∑_i X_{n,i}` converge in distribution to `N(0, v)`.

The proof compares characteristic functions. For each variable the second order Taylor remainder
of `x ↦ e^{ix}` is bounded by `2|x|³` near `0` and by `3x²` everywhere, which gives
`|φ_{n,i}(t) - 1 + t² σ²_{n,i} / 2| ≤ 2|t|³ ε σ²_{n,i} + 3t² E[X_{n,i}² 1{ε < |X_{n,i}|}]`. The
Lindeberg condition forces `max_i σ²_{n,i} → 0`, and the product of the characteristic functions is
compared with `∏_i exp(-t² σ²_{n,i} / 2) = exp(-t² ∑_i σ²_{n,i} / 2)` through
`|∏ a_i - ∏ b_i| ≤ ∑ |a_i - b_i|` for complex numbers of modulus at most one. Lévy's continuity
theorem concludes.

## Main definitions

* `CausalInference.TriangularArray.taylorRemainder`: `e^{ix} - 1 - ix + x²/2`.

## Main results

* `CausalInference.TriangularArray.norm_taylorRemainder_le`: the two remainder bounds.
* `CausalInference.TriangularArray.norm_prod_sub_prod_le`: the product comparison.
* `CausalInference.TriangularArray.tendsto_prod_charFun`: the characteristic function limit for
  rows of laws.
* `CausalInference.TriangularArray.tendstoInDistribution_sum`: **the Lindeberg central limit
  theorem**.

## References

* J. W. Lindeberg (1922), *Eine neue Herleitung des Exponentialgesetzes in der
  Wahrscheinlichkeitsrechnung*, Mathematische Zeitschrift 15.
* A. W. van der Vaart (1998), *Asymptotic Statistics*, chapter 2.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace CausalInference

namespace TriangularArray

/-! ### The Taylor remainder of the characteristic function integrand -/

/-- The second order Taylor remainder `e^{ix} - 1 - ix + x²/2` of `x ↦ e^{ix}`. -/
noncomputable def taylorRemainder (x : ℝ) : ℂ :=
  Complex.exp (x * Complex.I) - 1 - x * Complex.I + ((x ^ 2 / 2 : ℝ) : ℂ)

/-- **The Taylor remainder bound**: `|e^{ix} - 1 - ix + x²/2|` is at most `2|x|³` and at most
`3x²`. The real part `cos x - 1 + x²/2` lies in `[0, x²/2]` and is at most `|x|⁴` near `0`; the
imaginary part `sin x - x` is at most `|x|³/6` and at most `1 + |x|` in absolute value. -/
theorem norm_taylorRemainder_le (x : ℝ) :
    ‖taylorRemainder x‖ ≤ 2 * |x| ^ 3 ∧ ‖taylorRemainder x‖ ≤ 3 * x ^ 2 := by
  have hre : (taylorRemainder x).re = Real.cos x - 1 + x ^ 2 / 2 := by
    simp only [taylorRemainder, Complex.add_re, Complex.sub_re, Complex.one_re, Complex.mul_re,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
      Complex.exp_ofReal_mul_I_re]
    ring
  have him : (taylorRemainder x).im = Real.sin x - x := by
    simp only [taylorRemainder, Complex.add_im, Complex.sub_im, Complex.one_im, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
      Complex.exp_ofReal_mul_I_im]
    ring
  have hn := Complex.norm_le_abs_re_add_abs_im (taylorRemainder x)
  rw [hre, him] at hn
  have hc1 := Real.cos_le_one x
  have hc2 := Real.one_sub_sq_div_two_le_cos (x := x)
  have hs := Real.abs_sub_sin_le x
  have hs1 := Real.abs_sin_le_one x
  have ha := abs_nonneg x
  have hsq : x ^ 2 = |x| ^ 2 := (sq_abs x).symm
  have hre0 : |Real.cos x - 1 + x ^ 2 / 2| = Real.cos x - 1 + x ^ 2 / 2 :=
    abs_of_nonneg (by linarith)
  have him1 : |Real.sin x - x| ≤ |x| ^ 3 / 6 := by rwa [abs_sub_comm]
  have him2 : |Real.sin x - x| ≤ 1 + |x| := by
    have := abs_sub (Real.sin x) x
    linarith
  rw [hre0] at hn
  rcases le_or_gt |x| 1 with h1 | h1
  · have hcb := Real.cos_bound h1
    have h4 : |x| ^ 4 ≤ |x| ^ 3 := pow_le_pow_of_le_one ha h1 (by norm_num)
    have h3 : |x| ^ 3 ≤ |x| ^ 2 := pow_le_pow_of_le_one ha h1 (by norm_num)
    have hre4 : Real.cos x - 1 + x ^ 2 / 2 ≤ |x| ^ 4 * (5 / 96) := by
      have := (abs_le.1 hcb).2
      linarith
    constructor
    · nlinarith
    · nlinarith
  · have h3 : |x| ^ 2 ≤ |x| ^ 3 := pow_le_pow_right₀ h1.le (by norm_num)
    have h2 : |x| ≤ |x| ^ 2 := by nlinarith
    constructor
    · nlinarith
    · nlinarith

/-! ### One variable -/

section OneLaw

variable {ν : Measure ℝ} [IsProbabilityMeasure ν]

/-- **Second order expansion of a characteristic function.** For a centered law `ν` on `ℝ` with a
finite second moment, `φ(t) - 1 + t² E[X²] / 2 = E[R(tX)]` with `R` the Taylor remainder. -/
theorem charFun_sub_one_add_eq_integral (h2 : MemLp (fun x : ℝ ↦ x) 2 ν)
    (h0 : ∫ x, x ∂ν = 0) (t : ℝ) :
    charFun ν t - 1 + ((t ^ 2 / 2 * ∫ x, x ^ 2 ∂ν : ℝ) : ℂ) =
      ∫ x, taylorRemainder (t * x) ∂ν := by
  have hfi : Integrable (fun x : ℝ ↦ x) ν := h2.integrable one_le_two
  have hf2 : Integrable (fun x : ℝ ↦ x ^ 2) ν := h2.integrable_sq
  have h1 : Integrable (fun x : ℝ ↦ Complex.exp (((t * x : ℝ) : ℂ) * Complex.I)) ν := by
    refine Integrable.of_bound (by fun_prop) 1 (ae_of_all _ fun x ↦ ?_)
    rw [Complex.norm_exp_ofReal_mul_I]
  have hb : Integrable (fun x : ℝ ↦ ((t * x : ℝ) : ℂ) * Complex.I) ν :=
    (hfi.const_mul t).ofReal.mul_const _
  have hc0 : Integrable (fun x : ℝ ↦ (t * x) ^ 2 / 2) ν :=
    (hf2.const_mul (t ^ 2 / 2)).congr (ae_of_all _ fun x ↦ by
      change t ^ 2 / 2 * x ^ 2 = (t * x) ^ 2 / 2
      ring)
  have hc : Integrable (fun x : ℝ ↦ (((t * x) ^ 2 / 2 : ℝ) : ℂ)) ν := hc0.ofReal
  have hab : Integrable (fun x : ℝ ↦ Complex.exp (((t * x : ℝ) : ℂ) * Complex.I) - 1) ν :=
    h1.sub (integrable_const 1)
  have habb : Integrable (fun x : ℝ ↦ Complex.exp (((t * x : ℝ) : ℂ) * Complex.I) - 1 -
      ((t * x : ℝ) : ℂ) * Complex.I) ν := hab.sub hb
  have hcf : charFun ν t = ∫ x, Complex.exp (((t * x : ℝ) : ℂ) * Complex.I) ∂ν := by
    rw [charFun_apply_real]
    push_cast
    rfl
  simp only [taylorRemainder]
  rw [integral_add habb hc, integral_sub hab hb, integral_sub h1 (integrable_const 1),
    integral_mul_const, integral_complex_ofReal, integral_complex_ofReal, ← hcf,
    integral_const_mul, h0, integral_const]
  have hq : ∫ x, (t * x) ^ 2 / 2 ∂ν = t ^ 2 / 2 * ∫ x, x ^ 2 ∂ν := by
    rw [← integral_const_mul]
    exact integral_congr_ae (ae_of_all _ fun x ↦ by ring)
  rw [hq]
  simp

/-- **The Lindeberg bound for one variable.** For a centered law `ν` with a finite second moment
and `ε > 0`, `|φ(t) - 1 + t² E[X²] / 2| ≤ 2|t|³ ε E[X²] + 3t² E[X² 1{ε < |X|}]`. Split at
`|x| ≤ ε` and use the cubic remainder bound inside and the quadratic one outside. -/
theorem norm_charFun_sub_le (h2 : MemLp (fun x : ℝ ↦ x) 2 ν) (h0 : ∫ x, x ∂ν = 0) (t : ℝ)
    {ε : ℝ} (hε : 0 < ε) :
    ‖charFun ν t - 1 + ((t ^ 2 / 2 * ∫ x, x ^ 2 ∂ν : ℝ) : ℂ)‖ ≤
      2 * |t| ^ 3 * ε * ∫ x, x ^ 2 ∂ν + 3 * t ^ 2 * ∫ x in {x | ε < |x|}, x ^ 2 ∂ν := by
  rw [charFun_sub_one_add_eq_integral h2 h0 t]
  have hf2 : Integrable (fun x : ℝ ↦ x ^ 2) ν := h2.integrable_sq
  set A : Set ℝ := {x | ε < |x|} with hA
  have hAm : MeasurableSet A := measurableSet_lt measurable_const (by fun_prop)
  set g : ℝ → ℝ := fun x ↦ 2 * |t| ^ 3 * ε * x ^ 2 + 3 * t ^ 2 * A.indicator (fun x ↦ x ^ 2) x
    with hg
  have hgi : Integrable g ν :=
    (hf2.const_mul _).add (((integrable_indicator_iff hAm).2 hf2.integrableOn).const_mul _)
  have hpt : ∀ x, ‖taylorRemainder (t * x)‖ ≤ g x := by
    intro x
    obtain ⟨hc, hq⟩ := norm_taylorRemainder_le (t * x)
    have ht := abs_nonneg t
    have hxa := abs_nonneg x
    have hsq : x ^ 2 = |x| ^ 2 := (sq_abs x).symm
    by_cases hx : x ∈ A
    · have hind : A.indicator (fun x ↦ x ^ 2) x = x ^ 2 := Set.indicator_of_mem hx _
      have h6 : 0 ≤ 2 * |t| ^ 3 * ε * x ^ 2 := by positivity
      simp only [hg, hind]
      nlinarith
    · have hind : A.indicator (fun x ↦ x ^ 2) x = 0 := Set.indicator_of_notMem hx _
      have hle : |x| ≤ ε := by
        simp only [hA, Set.mem_ofPred_eq, not_lt] at hx
        exact hx
      have hc' : 2 * |t * x| ^ 3 = 2 * |t| ^ 3 * |x| ^ 2 * |x| := by
        rw [abs_mul]
        ring
      have h5 : 2 * |t| ^ 3 * |x| ^ 2 * |x| ≤ 2 * |t| ^ 3 * |x| ^ 2 * ε :=
        mul_le_mul_of_nonneg_left hle (by positivity)
      simp only [hg, hind]
      rw [← hsq] at h5 hc'
      nlinarith
  refine (norm_integral_le_of_norm_le hgi (ae_of_all _ hpt)).trans (le_of_eq ?_)
  rw [hg, integral_add (hf2.const_mul _)
      (((integrable_indicator_iff hAm).2 hf2.integrableOn).const_mul _),
    integral_const_mul, integral_const_mul, integral_indicator hAm]

/-- **A variance below a threshold plus a Lindeberg term.** For every `ε`,
`E[X²] ≤ ε² + E[X² 1{ε < |X|}]`. -/
theorem integral_sq_le_add_setIntegral (h2 : MemLp (fun x : ℝ ↦ x) 2 ν) (ε : ℝ) :
    ∫ x, x ^ 2 ∂ν ≤ ε ^ 2 + ∫ x in {x | ε < |x|}, x ^ 2 ∂ν := by
  have hf2 : Integrable (fun x : ℝ ↦ x ^ 2) ν := h2.integrable_sq
  have hAm : MeasurableSet {x : ℝ | ε < |x|} :=
    measurableSet_lt measurable_const (by fun_prop)
  rw [← integral_indicator hAm]
  have hbd : Integrable (fun x : ℝ ↦ ε ^ 2 + {x : ℝ | ε < |x|}.indicator (fun x ↦ x ^ 2) x) ν :=
    (integrable_const _).add ((integrable_indicator_iff hAm).2 hf2.integrableOn)
  calc ∫ x, x ^ 2 ∂ν ≤ ∫ x, (ε ^ 2 + {x : ℝ | ε < |x|}.indicator (fun x ↦ x ^ 2) x) ∂ν := by
        refine integral_mono hf2 hbd fun x ↦ ?_
        by_cases hx : ε < |x|
        · simp only [Set.indicator_of_mem (show x ∈ {x : ℝ | ε < |x|} from hx)]
          nlinarith
        · simp only [Set.indicator_of_notMem (show x ∉ {x : ℝ | ε < |x|} from hx), add_zero]
          have : |x| ≤ ε := not_lt.1 hx
          have hsq : x ^ 2 = |x| ^ 2 := (sq_abs x).symm
          rw [hsq]
          exact pow_le_pow_left₀ (abs_nonneg x) this 2
    _ = ε ^ 2 + ∫ x, {x : ℝ | ε < |x|}.indicator (fun x ↦ x ^ 2) x ∂ν := by
        rw [integral_add (integrable_const _) ((integrable_indicator_iff hAm).2
          hf2.integrableOn), integral_const, probReal_univ, one_smul]

end OneLaw

/-! ### Products of complex numbers in the unit disc -/

/-- **Product comparison.** For complex numbers `a i`, `b i` of modulus at most one,
`|∏ a_i - ∏ b_i| ≤ ∑ |a_i - b_i|`. Induction on the finite index set. -/
theorem norm_prod_sub_prod_le {ι : Type*} (s : Finset ι) {a b : ι → ℂ}
    (ha : ∀ i ∈ s, ‖a i‖ ≤ 1) (hb : ∀ i ∈ s, ‖b i‖ ≤ 1) :
    ‖∏ i ∈ s, a i - ∏ i ∈ s, b i‖ ≤ ∑ i ∈ s, ‖a i - b i‖ := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert j s hj ih =>
    rw [Finset.prod_insert hj, Finset.prod_insert hj, Finset.sum_insert hj]
    have ha' : ∀ i ∈ s, ‖a i‖ ≤ 1 := fun i hi ↦ ha i (Finset.mem_insert_of_mem hi)
    have hb' : ∀ i ∈ s, ‖b i‖ ≤ 1 := fun i hi ↦ hb i (Finset.mem_insert_of_mem hi)
    have hbp : ‖∏ i ∈ s, b i‖ ≤ 1 := by
      rw [norm_prod]
      exact Finset.prod_le_one₀ (fun _ _ ↦ norm_nonneg _) hb'
    have haj : ‖a j‖ ≤ 1 := ha j (Finset.mem_insert_self _ _)
    have e : a j * ∏ i ∈ s, a i - b j * ∏ i ∈ s, b i =
        a j * (∏ i ∈ s, a i - ∏ i ∈ s, b i) + (a j - b j) * ∏ i ∈ s, b i := by ring
    rw [e]
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, norm_mul]
    have h1 : ‖a j‖ * ‖∏ i ∈ s, a i - ∏ i ∈ s, b i‖ ≤ ∑ i ∈ s, ‖a i - b i‖ :=
      (mul_le_of_le_one_left (norm_nonneg _) haj).trans (ih ha' hb')
    have h2 : ‖a j - b j‖ * ‖∏ i ∈ s, b i‖ ≤ ‖a j - b j‖ :=
      mul_le_of_le_one_right (norm_nonneg _) hbp
    linarith

/-! ### Rows of laws -/

section Rows

variable {k : ℕ → ℕ} {ν : (n : ℕ) → Fin (k n) → Measure ℝ} [∀ n i, IsProbabilityMeasure (ν n i)]

/-- **The Lindeberg condition makes every variance of a row negligible**: for every `η > 0`,
eventually `σ²_{n,i} ≤ η` for all `i`. Take `ε² = η / 2` in
`σ²_{n,i} ≤ ε² + E[X_{n,i}² 1{ε < |X_{n,i}|}]`. -/
theorem eventually_forall_integral_sq_le (h2 : ∀ n i, MemLp (fun x : ℝ ↦ x) 2 (ν n i))
    (hL : ∀ ε, 0 < ε →
      Tendsto (fun n ↦ ∑ i, ∫ x in {x | ε < |x|}, x ^ 2 ∂ν n i) atTop (𝓝 0))
    {η : ℝ} (hη : 0 < η) : ∀ᶠ n in atTop, ∀ i, ∫ x, x ^ 2 ∂ν n i ≤ η := by
  set ε := √(η / 2) with hεdef
  have hε : 0 < ε := Real.sqrt_pos.2 (by positivity)
  have hε2 : ε ^ 2 = η / 2 := Real.sq_sqrt (by positivity)
  filter_upwards [(hL ε hε).eventually (gt_mem_nhds (half_pos hη))] with n hn i
  have h1 := integral_sq_le_add_setIntegral (h2 n i) ε
  have h3 : ∫ x in {x | ε < |x|}, x ^ 2 ∂ν n i ≤ ∑ j, ∫ x in {x | ε < |x|}, x ^ 2 ∂ν n j :=
    Finset.single_le_sum (f := fun j ↦ ∫ x in {x | ε < |x|}, x ^ 2 ∂ν n j)
      (fun j _ ↦ setIntegral_nonneg (measurableSet_lt measurable_const (by fun_prop))
        fun x _ ↦ sq_nonneg x) (Finset.mem_univ i)
  linarith

/-- **Characteristic functions of Lindeberg rows.** Let the laws `ν n i` on `ℝ` be centered with
finite second moments, with `∑_i E_{ν n i}[x²] → v` and the Lindeberg condition
`∑_i E_{ν n i}[x² 1{ε < |x|}] → 0` for every `ε > 0`. Then for every `t`,
`∏_i φ_{ν n i}(t) → exp(-t² v / 2)`. -/
theorem tendsto_prod_charFun (h2 : ∀ n i, MemLp (fun x : ℝ ↦ x) 2 (ν n i))
    (h0 : ∀ n i, ∫ x, x ∂ν n i = 0) {v : ℝ}
    (hv : Tendsto (fun n ↦ ∑ i, ∫ x, x ^ 2 ∂ν n i) atTop (𝓝 v))
    (hL : ∀ ε, 0 < ε →
      Tendsto (fun n ↦ ∑ i, ∫ x in {x | ε < |x|}, x ^ 2 ∂ν n i) atTop (𝓝 0))
    (t : ℝ) :
    Tendsto (fun n ↦ ∏ i, charFun (ν n i) t) atTop
      (𝓝 (Complex.exp (-((t ^ 2 / 2 * v : ℝ) : ℂ)))) := by
  set σ2 : (n : ℕ) → Fin (k n) → ℝ := fun n i ↦ ∫ x, x ^ 2 ∂ν n i with hσ2
  set s : ℕ → ℝ := fun n ↦ ∑ i, σ2 n i with hs
  set c : (n : ℕ) → Fin (k n) → ℝ := fun n i ↦ t ^ 2 / 2 * σ2 n i with hc
  have hσ0 : ∀ n i, 0 ≤ σ2 n i := fun n i ↦ integral_nonneg fun x ↦ sq_nonneg x
  have hc0 : ∀ n i, 0 ≤ c n i := fun n i ↦ mul_nonneg (by positivity) (hσ0 n i)
  set b : (n : ℕ) → Fin (k n) → ℂ := fun n i ↦ Complex.exp (-((c n i : ℝ) : ℂ)) with hb
  have hprodb : ∀ n, ∏ i, b n i = Complex.exp (-((t ^ 2 / 2 * s n : ℝ) : ℂ)) := by
    intro n
    rw [← Complex.exp_sum]
    congr 1
    simp only [hc, hs, Finset.mul_sum]
    push_cast
    rw [Finset.sum_neg_distrib]
  have hbn : ∀ n i, ‖b n i‖ ≤ 1 := fun n i ↦ by
    rw [hb, Complex.norm_exp]
    simp only [Complex.neg_re, Complex.ofReal_re]
    exact Real.exp_le_one_iff.2 (neg_nonpos.2 (hc0 n i))
  have han : ∀ n i, ‖charFun (ν n i) t‖ ≤ 1 := fun n i ↦ norm_charFun_le_one t
  have hexp : Tendsto (fun n ↦ ∏ i, b n i) atTop
      (𝓝 (Complex.exp (-((t ^ 2 / 2 * v : ℝ) : ℂ)))) := by
    simp only [hprodb]
    exact ((by fun_prop : Continuous fun x : ℝ ↦ Complex.exp (-(x : ℂ))).tendsto _).comp
      (hv.const_mul (t ^ 2 / 2))
  -- the sum of the differences tends to zero
  have hsum : Tendsto (fun n ↦ ∑ i, ‖charFun (ν n i) t - b n i‖) atTop (𝓝 0) := by
    refine tendsto_order.2 ⟨fun a ha ↦ Eventually.of_forall fun n ↦
      ha.trans_le (Finset.sum_nonneg fun _ _ ↦ norm_nonneg _), fun δ hδ ↦ ?_⟩
    set V := |v| + 1 with hV
    have hV0 : 0 < V := by positivity
    set ε := δ / (6 * (|t| ^ 3 + 1) * V) with hεd
    have hε : 0 < ε := by positivity
    set η := min (δ / (3 * (t ^ 4 + 1) * V)) (1 / (t ^ 2 + 1)) with hηd
    have hη : 0 < η := lt_min (by positivity) (by positivity)
    set ℓ := δ / (3 * (3 * t ^ 2 + 1)) with hℓ
    have hℓ0 : 0 < ℓ := by positivity
    have hsV : ∀ᶠ n in atTop, s n < V :=
      hv.eventually (gt_mem_nhds (by rw [hV]; linarith [le_abs_self v]))
    filter_upwards [hsV, (hL ε hε).eventually (gt_mem_nhds hℓ0),
      eventually_forall_integral_sq_le h2 hL hη] with n hsn hLn hmax
    set Ln : Fin (k n) → ℝ := fun i ↦ ∫ x in {x | ε < |x|}, x ^ 2 ∂ν n i with hLn'
    have hLi0 : ∀ i, 0 ≤ Ln i := fun i ↦ setIntegral_nonneg
      (measurableSet_lt measurable_const (by fun_prop)) fun x _ ↦ sq_nonneg x
    have hs0 : 0 ≤ s n := Finset.sum_nonneg fun i _ ↦ hσ0 n i
    have hcle : ∀ i, c n i ≤ t ^ 2 / 2 * η := fun i ↦
      mul_le_mul_of_nonneg_left (hmax i) (by positivity)
    have hc1 : ∀ i, c n i ≤ 1 := by
      intro i
      have h1 : η ≤ 1 / (t ^ 2 + 1) := min_le_right _ _
      have h2' : t ^ 2 / 2 * η ≤ t ^ 2 / 2 * (1 / (t ^ 2 + 1)) :=
        mul_le_mul_of_nonneg_left h1 (by positivity)
      have h3 : t ^ 2 / 2 * (1 / (t ^ 2 + 1)) ≤ 1 := by
        rw [mul_one_div, div_le_one (by positivity)]
        nlinarith [sq_nonneg t]
      linarith [hcle i]
    have hpt : ∀ i, ‖charFun (ν n i) t - b n i‖ ≤
        2 * |t| ^ 3 * ε * σ2 n i + 3 * t ^ 2 * Ln i + t ^ 2 / 2 * η * c n i := by
      intro i
      have e : charFun (ν n i) t - b n i = (charFun (ν n i) t - 1 + ((c n i : ℝ) : ℂ)) -
          (Complex.exp (-((c n i : ℝ) : ℂ)) - 1 - (-((c n i : ℝ) : ℂ))) := by
        rw [hb]
        ring
      rw [e]
      refine (norm_sub_le _ _).trans ?_
      have hA := norm_charFun_sub_le (h2 n i) (h0 n i) t hε
      have hnc : ‖-((c n i : ℝ) : ℂ)‖ = c n i := by
        rw [norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hc0 n i)]
      have hB := Complex.norm_exp_sub_one_sub_id_le (x := -((c n i : ℝ) : ℂ))
        (by rw [hnc]; exact hc1 i)
      rw [hnc] at hB
      have hB' : c n i ^ 2 ≤ t ^ 2 / 2 * η * c n i := by
        rw [sq]
        exact mul_le_mul_of_nonneg_right (hcle i) (hc0 n i)
      have hA' : ‖charFun (ν n i) t - 1 + ((c n i : ℝ) : ℂ)‖ ≤
          2 * |t| ^ 3 * ε * σ2 n i + 3 * t ^ 2 * Ln i := hA
      linarith
    have hbound : ∑ i, ‖charFun (ν n i) t - b n i‖ ≤
        2 * |t| ^ 3 * ε * s n + 3 * t ^ 2 * ∑ i, Ln i + t ^ 2 / 2 * η * (t ^ 2 / 2 * s n) := by
      refine (Finset.sum_le_sum fun i _ ↦ hpt i).trans (le_of_eq ?_)
      simp only [Finset.sum_add_distrib, ← Finset.mul_sum, hs, hc]
    have hLs : ∑ i, Ln i < ℓ := hLn
    have hLs0 : 0 ≤ ∑ i, Ln i := Finset.sum_nonneg fun i _ ↦ hLi0 i
    have k1 : 2 * |t| ^ 3 * ε * s n ≤ δ / 3 := by
      have hk : 2 * |t| ^ 3 * ε * V = δ / 3 * (|t| ^ 3 / (|t| ^ 3 + 1)) := by
        rw [hεd]
        field_simp
        ring
      have hq : |t| ^ 3 / (|t| ^ 3 + 1) ≤ 1 := (div_le_one (by positivity)).2 (by linarith)
      calc 2 * |t| ^ 3 * ε * s n ≤ 2 * |t| ^ 3 * ε * V :=
            mul_le_mul_of_nonneg_left hsn.le (by positivity)
        _ ≤ δ / 3 := by rw [hk]; exact mul_le_of_le_one_right (by positivity) hq
    have k2 : 3 * t ^ 2 * ∑ i, Ln i < δ / 3 := by
      have hk : (3 * t ^ 2 + 1) * ℓ = δ / 3 := by
        rw [hℓ]
        field_simp
      calc 3 * t ^ 2 * ∑ i, Ln i ≤ (3 * t ^ 2 + 1) * ∑ i, Ln i :=
            mul_le_mul_of_nonneg_right (by linarith) hLs0
        _ < (3 * t ^ 2 + 1) * ℓ := mul_lt_mul_of_pos_left hLs (by positivity)
        _ = δ / 3 := hk
    have k3 : t ^ 2 / 2 * η * (t ^ 2 / 2 * s n) ≤ δ / 3 := by
      have h1 : η ≤ δ / (3 * (t ^ 4 + 1) * V) := min_le_left _ _
      have hk : t ^ 4 / 4 * (δ / (3 * (t ^ 4 + 1) * V)) * V =
          δ / 3 * (t ^ 4 / (4 * (t ^ 4 + 1))) := by
        field_simp
      have hq : t ^ 4 / (4 * (t ^ 4 + 1)) ≤ 1 :=
        (div_le_one (by positivity)).2 (by nlinarith [pow_nonneg (sq_nonneg t) 2])
      calc t ^ 2 / 2 * η * (t ^ 2 / 2 * s n) = t ^ 4 / 4 * η * s n := by ring
        _ ≤ t ^ 4 / 4 * (δ / (3 * (t ^ 4 + 1) * V)) * V :=
            mul_le_mul (mul_le_mul_of_nonneg_left h1 (by positivity)) hsn.le hs0
              (by positivity)
        _ ≤ δ / 3 := by rw [hk]; exact mul_le_of_le_one_right (by positivity) hq
    linarith
  have hdiff : Tendsto (fun n ↦ ∏ i, charFun (ν n i) t - ∏ i, b n i) atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    exact squeeze_zero (fun _ ↦ norm_nonneg _)
      (fun n ↦ norm_prod_sub_prod_le _ (fun i _ ↦ han n i) (fun i _ ↦ hbn n i)) hsum
  simpa using hdiff.add hexp

end Rows

/-! ### The Lindeberg central limit theorem -/

/-- **The Lindeberg central limit theorem.** For each `n` let `X n 0, …, X n (k n - 1)` be
independent real random variables on a probability space `(Ω n, P n)`, centered and square
integrable, not necessarily identically distributed. If the variances sum to a limit,
`∑_i E[X_{n,i}²] → v`, and the Lindeberg condition `∑_i E[X_{n,i}² 1{ε < |X_{n,i}|}] → 0` holds for
every `ε > 0`, then the row sums `∑_i X_{n,i}` converge in distribution to every variable `Y` with
law `N(0, v)`. -/
theorem tendstoInDistribution_sum {Ω : ℕ → Type*} {mΩ : ∀ n, MeasurableSpace (Ω n)}
    {P : (n : ℕ) → Measure (Ω n)} [∀ n, IsProbabilityMeasure (P n)] {k : ℕ → ℕ}
    {X : (n : ℕ) → Fin (k n) → Ω n → ℝ} (hind : ∀ n, iIndepFun (X n) (P n))
    (h2 : ∀ n i, MemLp (X n i) 2 (P n)) (h0 : ∀ n i, ∫ ω, X n i ω ∂P n = 0) {v : ℝ}
    (hv : Tendsto (fun n ↦ ∑ i, ∫ ω, X n i ω ^ 2 ∂P n) atTop (𝓝 v))
    (hL : ∀ ε, 0 < ε → Tendsto (fun n ↦ ∑ i,
      ∫ ω, {x : ℝ | ε < |x|}.indicator (fun x ↦ x ^ 2) (X n i ω) ∂P n) atTop (𝓝 0))
    {Ω' : Type*} {mΩ' : MeasurableSpace Ω'} {P' : Measure Ω'} [IsProbabilityMeasure P']
    {Y : Ω' → ℝ} (hY : HasLaw Y (gaussianReal 0 v.toNNReal) P') :
    TendstoInDistribution (fun n ω ↦ ∑ i, X n i ω) atTop Y P P' := by
  have hXm : ∀ n i, AEMeasurable (X n i) (P n) := fun n i ↦
    (h2 n i).aestronglyMeasurable.aemeasurable
  set ν : (n : ℕ) → Fin (k n) → Measure ℝ := fun n i ↦ (P n).map (X n i) with hν
  have hνp : ∀ n i, IsProbabilityMeasure (ν n i) := fun n i ↦
    inferInstance
  have hm2 : ∀ n i, MemLp (fun x : ℝ ↦ x) 2 (ν n i) := fun n i ↦
    (memLp_map_measure_iff aestronglyMeasurable_id (hXm n i)).2 (h2 n i)
  have hint : ∀ n i {g : ℝ → ℝ}, Measurable g → ∫ x, g x ∂ν n i = ∫ ω, g (X n i ω) ∂P n :=
    fun n i g hg ↦ integral_map (hXm n i) hg.aestronglyMeasurable
  have hAm : ∀ ε : ℝ, MeasurableSet {x : ℝ | ε < |x|} := fun ε ↦
    measurableSet_lt measurable_const (by fun_prop)
  have h0' : ∀ n i, ∫ x, x ∂ν n i = 0 := fun n i ↦ by
    rw [hint n i (g := fun x ↦ x) measurable_id]
    exact h0 n i
  have hv' : Tendsto (fun n ↦ ∑ i, ∫ x, x ^ 2 ∂ν n i) atTop (𝓝 v) := by
    refine hv.congr fun n ↦ Finset.sum_congr rfl fun i _ ↦ ?_
    rw [hint n i (by fun_prop)]
  have hL' : ∀ ε, 0 < ε →
      Tendsto (fun n ↦ ∑ i, ∫ x in {x | ε < |x|}, x ^ 2 ∂ν n i) atTop (𝓝 0) := by
    intro ε hε
    refine (hL ε hε).congr fun n ↦ Finset.sum_congr rfl fun i _ ↦ ?_
    rw [← integral_indicator (hAm ε),
      hint n i ((by fun_prop : Measurable fun x : ℝ ↦ x ^ 2).indicator (hAm ε))]
  have hv0 : 0 ≤ v := ge_of_tendsto' hv fun n ↦ Finset.sum_nonneg fun i _ ↦
    integral_nonneg fun ω ↦ sq_nonneg _
  refine TendstoInDistribution.of_tendsto_charFun
    (fun n ↦ Finset.aemeasurable_fun_sum _ fun i _ ↦ hXm n i) hY.aemeasurable fun t ↦ ?_
  rw [hY.map_eq, charFun_gaussianReal]
  have hlim := tendsto_prod_charFun hm2 h0' hv' hL' t
  have heq : Complex.exp (-((t ^ 2 / 2 * v : ℝ) : ℂ)) =
      Complex.exp (t * ((0 : ℝ) : ℂ) * Complex.I - ((v.toNNReal : ℝ) : ℂ) * t ^ 2 / 2) := by
    congr 1
    rw [Real.coe_toNNReal v hv0]
    push_cast
    ring
  rw [← heq]
  refine hlim.congr fun n ↦ ?_
  rw [(hind n).charFun_map_fun_sum_eq_prod (hXm n), Finset.prod_apply]

end TriangularArray

end CausalInference
