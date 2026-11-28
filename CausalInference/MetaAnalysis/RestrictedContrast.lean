/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.MetaAnalysis.ConjugacyKernel
public import CausalInference.MetaAnalysis.RestrictedLikelihoodMaximizer
public import CausalInference.MetaAnalysis.CochranQ
public import CausalInference.Estimation.GaussianLinearImage
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-!
# Restricted likelihood through error contrasts

In the linear model `y ~ N(X β, V)` an **error contrast** is a matrix `K` with `Kᵀ X = 0`. The
restricted (residual) likelihood of Patterson and Thompson (1971) is the likelihood of `Kᵀ y`
(Harville 1974). With `contrastLogLik K V y = -½ log det(Kᵀ V K) - ½ (Kᵀ y)ᵀ (Kᵀ V K)⁻¹ (Kᵀ y)`,
the Gaussian log density of `Kᵀ y` under `N(0, Kᵀ V K)` up to the constant `-(m/2) log 2π`:

* **The law of `Kᵀ y` does not depend on `β`** (`map_contrast_multivariateGaussian`): under
  `N(X β, V)`, `Kᵀ y ~ N(0, Kᵀ V K)` for every `β`; and `contrastLogLik K V (y + X β)` equals
  `contrastLogLik K V y` (`contrastLogLik_add_mulVec`).
* **Invariance to the choice of contrasts** (`contrastLogLik_mul`): replacing `K` by `K A` with
  `A` invertible changes the restricted log likelihood by the constant `-log |det A|`, provided
  `det(Kᵀ V K) ≠ 0`.
* **One sample with the mean as the only fixed effect** (`X = 1`, `V = s I`). For every `K` with
  `Kᵀ 1 = 0`, `det(Kᵀ K) ≠ 0` and `ker Kᵀ = span{1}`: `K` has `n - 1` columns
  (`card_add_one_of_contrast`), the quadratic form is the sum of squares
  `S = ∑ (yᵢ - ȳ)²` (`contrast_quadForm_eq_regSxx`), and
  `contrastLogLik K (s I) y = -((n-1)/2) log s - ½ log det(Kᵀ K) - S/(2s)`
  (`contrastLogLik_smul_one`). This equals the library's `restrictedLogLik` with equal variances
  up to a constant that depends on `K` only (`contrastLogLik_eq_restrictedLogLik`).
* **REML and ML variance estimates** (`contrastLogLik_smul_one_lt`, `gaussLogLik_lt`): if
  `S > 0`, the restricted likelihood has the unique maximizer `s = S/(n-1)`, and the full
  likelihood of `N(μ, s)` has the unique maximizer `(ȳ, S/n)`.
* **Their expectations** (`integral_regSxx_div`): for square integrable, pairwise uncorrelated
  observations with common mean and variance `σ² > 0`, `E[S/(n-1)] = σ²` and
  `E[S/n] = (n-1)/n · σ²`: the restricted estimate is unbiased, the full one is biased downward.
* **`S > 0` almost surely** (`ae_regSxx_pos`) under i.i.d. `N(θ, σ²)`, `σ² > 0`, `n ≥ 2`: then
  both maximizers exist almost surely.

The identity with `restrictedLogLik` for unequal variances `V = diag(vᵢ + t)` needs the
determinant and quadratic form identities of Harville (1974); only the equal variance case is
proved here.

## Main definitions

* `contrastLogLik`, `gaussLogLik`.

## Main results

* `map_contrast_multivariateGaussian`, `contrastLogLik_add_mulVec`, `contrastLogLik_mul`,
  `contrast_quadForm_eq_regSxx`, `card_add_one_of_contrast`, `contrastLogLik_smul_one`,
  `contrastLogLik_eq_restrictedLogLik`, `neg_log_sub_div_lt`, `contrastLogLik_smul_one_lt`,
  `gaussLogLik_lt`, `integral_regSxx_div`, `ae_regSxx_pos`.

## References

* H. D. Patterson and R. Thompson, *Recovery of inter-block information when block sizes are
  unequal*, Biometrika 58 (1971).
* D. A. Harville, *Bayesian inference for variance components using only error contrasts*,
  Biometrika 61 (1974).
-/

@[expose] public section

namespace CausalInference

namespace MetaAnalysis

open MeasureTheory ProbabilityTheory Matrix
open scoped ENNReal NNReal

variable {n m p : Type*} [Fintype n] [Fintype m] [Fintype p] [DecidableEq n] [DecidableEq m]

/-- The **restricted log likelihood of the error contrasts** `Kᵀ y`:
`-½ log det(Kᵀ V K) - ½ (Kᵀ y)ᵀ (Kᵀ V K)⁻¹ (Kᵀ y)`, the log density of `N(0, Kᵀ V K)` at `Kᵀ y`
up to the constant `-(m/2) log 2π`. -/
noncomputable def contrastLogLik (K : Matrix n m ℝ) (V : Matrix n n ℝ) (y : n → ℝ) : ℝ :=
  -(1 / 2) * Real.log (Kᵀ * V * K).det -
    1 / 2 * ((Kᵀ *ᵥ y) ⬝ᵥ ((Kᵀ * V * K)⁻¹ *ᵥ (Kᵀ *ᵥ y)))

omit [DecidableEq n] in
/-- **The contrasts do not see the fixed effects**: if `Kᵀ X = 0`, then
`contrastLogLik K V (y + X β) = contrastLogLik K V y`. -/
theorem contrastLogLik_add_mulVec {K : Matrix n m ℝ} {X : Matrix n p ℝ} (hKX : Kᵀ * X = 0)
    (V : Matrix n n ℝ) (y : n → ℝ) (β : p → ℝ) :
    contrastLogLik K V (y + X *ᵥ β) = contrastLogLik K V y := by
  simp only [contrastLogLik, mulVec_add, mulVec_mulVec, hKX, zero_mulVec, add_zero]

/-- **The law of the error contrasts does not depend on `β`**: if `V` is positive semidefinite
and `Kᵀ X = 0`, then under `N(X β, V)` the contrasts `Kᵀ y` have the law `N(0, Kᵀ V K)`, for
every `β`. -/
theorem map_contrast_multivariateGaussian {K : Matrix n m ℝ} {X : Matrix n p ℝ}
    (hKX : Kᵀ * X = 0) {V : Matrix n n ℝ} (hV : V.PosSemidef) (β : p → ℝ) :
    (multivariateGaussian (WithLp.toLp 2 (X *ᵥ β)) V).map (matrixCLM Kᵀ) =
      multivariateGaussian 0 (Kᵀ * V * K) := by
  classical
  rw [multivariateGaussian_map_matrixCLM hV _ Kᵀ, transpose_transpose, matrixCLM_apply]
  congr 1
  simp [mulVec_mulVec, hKX]

omit [DecidableEq n] in
/-- **Invariance to the choice of contrasts**: for `A` invertible and `det(Kᵀ V K) ≠ 0`, the
contrasts `K A` give the restricted log likelihood of `K` shifted by the constant
`-log |det A|`. -/
theorem contrastLogLik_mul (K : Matrix n m ℝ) (V : Matrix n n ℝ) {A : Matrix m m ℝ}
    (hA : A.det ≠ 0) (hM : (Kᵀ * V * K).det ≠ 0) (y : n → ℝ) :
    contrastLogLik (K * A) V y = contrastLogLik K V y - Real.log |A.det| := by
  set M := Kᵀ * V * K
  have hAu : IsUnit A.det := isUnit_iff_ne_zero.2 hA
  have hAtu : IsUnit Aᵀ.det := by rwa [det_transpose]
  have hMA : (K * A)ᵀ * V * (K * A) = Aᵀ * M * A := by
    simp only [M, transpose_mul, Matrix.mul_assoc]
  have hdet : (Aᵀ * M * A).det = A.det ^ 2 * M.det := by
    rw [det_mul, det_mul, det_transpose]; ring
  have hlog : Real.log (A.det ^ 2 * M.det) = 2 * Real.log |A.det| + Real.log M.det := by
    rw [Real.log_mul (pow_ne_zero 2 hA) hM, Real.log_pow, Real.log_abs]
    push_cast; ring
  have hinv : (Aᵀ * M * A)⁻¹ = A⁻¹ * M⁻¹ * (Aᵀ)⁻¹ := by
    rw [Matrix.mul_inv_rev, Matrix.mul_inv_rev, Matrix.mul_assoc]
  have hquad : ((K * A)ᵀ *ᵥ y) ⬝ᵥ ((Aᵀ * M * A)⁻¹ *ᵥ ((K * A)ᵀ *ᵥ y)) =
      (Kᵀ *ᵥ y) ⬝ᵥ (M⁻¹ *ᵥ (Kᵀ *ᵥ y)) := by
    have h1 : (K * A)ᵀ *ᵥ y = Aᵀ *ᵥ (Kᵀ *ᵥ y) := by
      rw [transpose_mul, mulVec_mulVec]
    have h2 : ∀ u : m → ℝ, (A⁻¹ * M⁻¹ * (Aᵀ)⁻¹) *ᵥ (Aᵀ *ᵥ u) = A⁻¹ *ᵥ (M⁻¹ *ᵥ u) := by
      intro u
      rw [mulVec_mulVec, Matrix.mul_assoc (A⁻¹ * M⁻¹), nonsing_inv_mul _ hAtu, Matrix.mul_one,
        ← mulVec_mulVec]
    have h3 : ∀ u z : m → ℝ, (Aᵀ *ᵥ u) ⬝ᵥ (A⁻¹ *ᵥ z) = u ⬝ᵥ z := by
      intro u z
      rw [dotProduct_mulVec, mulVec_transpose, vecMul_vecMul, mul_nonsing_inv _ hAu, vecMul_one]
    rw [h1, hinv, h2, h3]
  simp only [contrastLogLik, hMA, hdet, hlog, hquad]
  ring

/-! ### One sample: the mean as the only fixed effect -/

omit [DecidableEq n] in
/-- **The quadratic form of the contrasts is the sum of squares**: if `Kᵀ 1 = 0`,
`det(Kᵀ K) ≠ 0` and every `z` with `Kᵀ z = 0` is constant, then
`(Kᵀ y)ᵀ (Kᵀ K)⁻¹ (Kᵀ y) = ∑ (yᵢ - ȳ)²`. Proof: `p = K (Kᵀ K)⁻¹ Kᵀ y` has `Kᵀ (y - p) = 0`, so
`y - p` is constant, and `∑ pᵢ = 0` fixes the constant at `ȳ`. -/
theorem contrast_quadForm_eq_regSxx [Nonempty n] {K : Matrix n m ℝ}
    (hK1 : Kᵀ *ᵥ (fun _ => 1) = 0) (hKK : (Kᵀ * K).det ≠ 0)
    (hker : ∀ z : n → ℝ, Kᵀ *ᵥ z = 0 → ∃ c : ℝ, z = fun _ => c) (y : n → ℝ) :
    (Kᵀ *ᵥ y) ⬝ᵥ ((Kᵀ * K)⁻¹ *ᵥ (Kᵀ *ᵥ y)) = regSxx y := by
  have hGu : IsUnit (Kᵀ * K).det := isUnit_iff_ne_zero.2 hKK
  set w := (Kᵀ * K)⁻¹ *ᵥ (Kᵀ *ᵥ y) with hw
  set q := K *ᵥ w with hqdef
  have hKq : Kᵀ *ᵥ q = Kᵀ *ᵥ y := by
    rw [hqdef, hw, mulVec_mulVec, mulVec_mulVec, mul_nonsing_inv _ hGu, one_mulVec]
  have hq : Kᵀ *ᵥ (y - q) = 0 := by rw [mulVec_sub, hKq, sub_self]
  obtain ⟨c, hc⟩ := hker _ hq
  have hsumq : ∑ i, q i = 0 := by
    have : (fun _ : n => (1 : ℝ)) ⬝ᵥ q = 0 := by
      rw [hqdef, dotProduct_mulVec, ← mulVec_transpose, hK1, zero_dotProduct]
    simpa [dotProduct] using this
  have hyq : ∀ i, y i = q i + c := fun i => by
    have := congrFun hc i
    simp only [Pi.sub_apply] at this
    linarith
  have hk : (Fintype.card n : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hmean : regMean y = c := by
    rw [regMean, Finset.sum_congr rfl fun i _ => hyq i, Finset.sum_add_distrib, hsumq,
      Finset.sum_const, Finset.card_univ, nsmul_eq_mul, zero_add]
    field_simp
  have hlhs : (Kᵀ *ᵥ y) ⬝ᵥ w = y ⬝ᵥ q := by
    rw [hqdef, dotProduct_mulVec y K, ← mulVec_transpose]
  rw [hlhs, regSxx, hmean]
  simp only [dotProduct]
  have : ∀ i, (y i - c) ^ 2 = y i * q i - c * q i := fun i => by rw [hyq i]; ring
  rw [Finset.sum_congr rfl fun i _ => this i, Finset.sum_sub_distrib, ← Finset.mul_sum, hsumq,
    mul_zero, sub_zero]

omit [DecidableEq n] in
/-- **A full set of contrasts has `n - 1` columns**: under the hypotheses of
`contrast_quadForm_eq_regSxx`, `card m + 1 = card n`. Proof: `Kᵀ` maps onto `ℝᵐ` (it has the
right inverse `K (Kᵀ K)⁻¹`) and its kernel is the line of constants; rank and nullity. -/
theorem card_add_one_of_contrast [Nonempty n] {K : Matrix n m ℝ}
    (hK1 : Kᵀ *ᵥ (fun _ => 1) = 0) (hKK : (Kᵀ * K).det ≠ 0)
    (hker : ∀ z : n → ℝ, Kᵀ *ᵥ z = 0 → ∃ c : ℝ, z = fun _ => c) :
    Fintype.card m + 1 = Fintype.card n := by
  classical
  set f := Matrix.toLin' Kᵀ
  have hGu : IsUnit (Kᵀ * K).det := isUnit_iff_ne_zero.2 hKK
  have hrange : LinearMap.range f = ⊤ := by
    refine LinearMap.range_eq_top.2 fun z => ⟨K *ᵥ ((Kᵀ * K)⁻¹ *ᵥ z), ?_⟩
    simp only [f, Matrix.toLin'_apply, mulVec_mulVec, ← Matrix.mul_assoc,
      mul_nonsing_inv _ hGu, one_mulVec]
  have hkerf : LinearMap.ker f = Submodule.span ℝ {fun _ => (1 : ℝ)} := by
    ext z
    simp only [LinearMap.mem_ker, f, Matrix.toLin'_apply, Submodule.mem_span_singleton]
    constructor
    · intro hz
      obtain ⟨c, hc⟩ := hker z hz
      exact ⟨c, by rw [hc]; funext; simp⟩
    · rintro ⟨c, rfl⟩
      rw [mulVec_smul, hK1, smul_zero]
  have h := LinearMap.finrank_range_add_finrank_ker f
  rw [hrange, hkerf, finrank_span_singleton (fun h => by
      simpa using congrFun h (Classical.arbitrary n)), finrank_top,
    Module.finrank_fintype_fun_eq_card,
    Module.finrank_fintype_fun_eq_card] at h
  exact h

/-- **The restricted log likelihood of one sample**: for contrasts as in
`contrast_quadForm_eq_regSxx` and `s > 0`,
`contrastLogLik K (s I) y = -((n-1)/2) log s - ½ log det(Kᵀ K) - S/(2s)`, `S = ∑ (yᵢ - ȳ)²`. -/
theorem contrastLogLik_smul_one [Nonempty n] {K : Matrix n m ℝ}
    (hK1 : Kᵀ *ᵥ (fun _ => 1) = 0) (hKK : (Kᵀ * K).det ≠ 0)
    (hker : ∀ z : n → ℝ, Kᵀ *ᵥ z = 0 → ∃ c : ℝ, z = fun _ => c) {s : ℝ} (hs : 0 < s)
    (y : n → ℝ) :
    contrastLogLik K (s • 1) y = -(((Fintype.card n : ℝ) - 1) / 2) * Real.log s -
      1 / 2 * Real.log (Kᵀ * K).det - regSxx y / (2 * s) := by
  have hcard : (Fintype.card m : ℝ) = Fintype.card n - 1 := by
    have := card_add_one_of_contrast hK1 hKK hker
    have : (Fintype.card m : ℝ) + 1 = Fintype.card n := by exact_mod_cast this
    linarith
  have hM : Kᵀ * (s • (1 : Matrix n n ℝ)) * K = s • (Kᵀ * K) := by
    rw [Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul]
  have hGu : IsUnit (Kᵀ * K).det := isUnit_iff_ne_zero.2 hKK
  have hinv : (s • (Kᵀ * K))⁻¹ = s⁻¹ • (Kᵀ * K)⁻¹ := by
    refine inv_eq_left_inv ?_
    rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, inv_mul_cancel₀ hs.ne', one_smul,
      nonsing_inv_mul _ hGu]
  have hquad := contrast_quadForm_eq_regSxx hK1 hKK hker y
  simp only [contrastLogLik, hM, hinv, smul_mulVec, dotProduct_smul, hquad, det_smul,
    smul_eq_mul]
  rw [Real.log_mul (pow_ne_zero _ hs.ne') hKK, Real.log_pow, hcard]
  field_simp
  ring

/-- **The contrast likelihood is the library's restricted likelihood up to a constant**: with
equal variances `vᵢ = v` and `v + t > 0`, for contrasts as in `contrast_quadForm_eq_regSxx`,
`contrastLogLik K ((v + t) I) y = restrictedLogLik v y t + ½ log n - ½ log det(Kᵀ K)`; the
constant depends on `K` and `n` only. -/
theorem contrastLogLik_eq_restrictedLogLik [Nonempty n] {K : Matrix n m ℝ}
    (hK1 : Kᵀ *ᵥ (fun _ => 1) = 0) (hKK : (Kᵀ * K).det ≠ 0)
    (hker : ∀ z : n → ℝ, Kᵀ *ᵥ z = 0 → ∃ c : ℝ, z = fun _ => c) {v t : ℝ} (hvt : 0 < v + t)
    (y : n → ℝ) :
    contrastLogLik K ((v + t) • 1) y = restrictedLogLik (fun _ : n => v) y t +
      1 / 2 * Real.log (Fintype.card n) - 1 / 2 * Real.log (Kᵀ * K).det := by
  rw [contrastLogLik_smul_one hK1 hKK hker hvt, restrictedLogLik_const hvt]
  ring

/-- **The profile `-(c/2) log s - S/(2s)` has the unique maximizer `S/c`** on `(0, ∞)`, for
`c > 0` and `S > 0`. Proof: `log x ≤ x - 1`, with equality only at `x = 1`. -/
theorem neg_log_sub_div_lt {c S s : ℝ} (hc : 0 < c) (hS : 0 < S) (hs : 0 < s)
    (hne : s ≠ S / c) :
    -(c / 2) * Real.log s - S / (2 * s) < -(c / 2) * Real.log (S / c) - S / (2 * (S / c)) := by
  set x := S / (c * s)
  have hx : 0 < x := by positivity
  have hx1 : x ≠ 1 := by
    intro h
    apply hne
    have : S = c * s := by
      have := h; simp only [x] at this
      rwa [div_eq_one_iff_eq (by positivity)] at this
    rw [this]; field_simp
  have hlog := Real.log_lt_sub_one_of_pos hx hx1
  have hlx : Real.log x = Real.log (S / c) - Real.log s := by
    rw [show x = S / c / s by simp only [x]; field_simp, Real.log_div (by positivity) hs.ne']
  have h1 : S / (2 * s) = c / 2 * x := by simp only [x]; field_simp
  have h2 : S / (2 * (S / c)) = c / 2 := by field_simp
  rw [h1, h2]
  nlinarith

/-- **REML for one sample**: if `S = ∑ (yᵢ - ȳ)² > 0` and `K` is as in
`contrast_quadForm_eq_regSxx` (then `n ≥ 2` holds, since `S = 0` for one observation),
then `s ↦ contrastLogLik K (s I) y` has the unique
maximizer `S/(n-1)` on `(0, ∞)`. -/
theorem contrastLogLik_smul_one_lt [Nonempty n] {K : Matrix n m ℝ}
    (hK1 : Kᵀ *ᵥ (fun _ => 1) = 0) (hKK : (Kᵀ * K).det ≠ 0)
    (hker : ∀ z : n → ℝ, Kᵀ *ᵥ z = 0 → ∃ c : ℝ, z = fun _ => c)
    {y : n → ℝ} (hS : 0 < regSxx y) {s : ℝ} (hs : 0 < s)
    (hne : s ≠ regSxx y / (Fintype.card n - 1)) :
    contrastLogLik K (s • 1) y <
      contrastLogLik K ((regSxx y / (Fintype.card n - 1)) • 1) y := by
  have hn : 2 ≤ Fintype.card n := by
    by_contra h
    have h1 : Fintype.card n = 1 := le_antisymm (by omega) Fintype.card_pos
    obtain ⟨x, hx⟩ := Fintype.card_eq_one_iff.1 h1
    have hsum : ∀ i, ∑ j, y j = y i := fun i => by
      rw [Finset.sum_eq_single i (fun j _ hj => absurd ((hx j).trans (hx i).symm) hj)
        (fun h => absurd (Finset.mem_univ i) h)]
    have : regSxx y = 0 := by
      refine Finset.sum_eq_zero fun i _ => ?_
      rw [regMean, hsum i, h1, Nat.cast_one, div_one, sub_self]
      ring
    linarith
  have hn' : (0 : ℝ) < Fintype.card n - 1 := by
    have : (2 : ℝ) ≤ Fintype.card n := by exact_mod_cast hn
    linarith
  rw [contrastLogLik_smul_one hK1 hKK hker hs, contrastLogLik_smul_one hK1 hKK hker
    (by positivity)]
  have := neg_log_sub_div_lt hn' hS hs hne
  linarith

/-- The **log likelihood of an i.i.d. `N(μ, s)` sample**, up to the constant `-(n/2) log 2π`:
`-(n/2) log s - ∑ (yᵢ - μ)²/(2s)`. -/
noncomputable def gaussLogLik (y : n → ℝ) (μ s : ℝ) : ℝ :=
  -((Fintype.card n : ℝ) / 2) * Real.log s - (∑ i, (y i - μ) ^ 2) / (2 * s)

omit [DecidableEq n] in
/-- **ML for one sample**: if `S > 0`, the full likelihood of `N(μ, s)` has the unique maximizer
`(ȳ, S/n)` over `ℝ × (0, ∞)`. -/
theorem gaussLogLik_lt [Nonempty n] {y : n → ℝ} (hS : 0 < regSxx y) {μ s : ℝ} (hs : 0 < s)
    (hne : (μ, s) ≠ (regMean y, regSxx y / Fintype.card n)) :
    gaussLogLik y μ s < gaussLogLik y (regMean y) (regSxx y / Fintype.card n) := by
  have hk : (0 : ℝ) < Fintype.card n := by exact_mod_cast Fintype.card_pos
  have hsum : ∑ i, (y i - μ) ^ 2 = regSxx y + Fintype.card n * (regMean y - μ) ^ 2 := by
    have h0 : ∑ i, (y i - regMean y) = 0 := by
      rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, regMean]
      field_simp; ring
    rw [regSxx]
    have : ∀ i, (y i - μ) ^ 2 = (y i - regMean y) ^ 2 + 2 * (regMean y - μ) * (y i - regMean y)
        + (regMean y - μ) ^ 2 := fun i => by ring
    rw [Finset.sum_congr rfl fun i _ => this i, Finset.sum_add_distrib, Finset.sum_add_distrib,
      ← Finset.mul_sum, h0, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    ring
  have hle : gaussLogLik y μ s ≤ gaussLogLik y (regMean y) s := by
    simp only [gaussLogLik]
    rw [hsum]
    have : 0 ≤ Fintype.card n * (regMean y - μ) ^ 2 / (2 * s) := by positivity
    have e : (regSxx y + Fintype.card n * (regMean y - μ) ^ 2) / (2 * s) =
        regSxx y / (2 * s) + Fintype.card n * (regMean y - μ) ^ 2 / (2 * s) := by ring
    have e2 : ∑ i, (y i - regMean y) ^ 2 = regSxx y := rfl
    rw [e, e2]
    linarith
  have hval : ∀ t, gaussLogLik y (regMean y) t =
      -((Fintype.card n : ℝ) / 2) * Real.log t - regSxx y / (2 * t) := fun t => rfl
  by_cases hsn : s = regSxx y / Fintype.card n
  · have hμ : μ ≠ regMean y := fun h => hne (by rw [h, hsn])
    simp only [gaussLogLik]
    rw [hsum, ← hsn]
    have : 0 < Fintype.card n * (regMean y - μ) ^ 2 / (2 * s) := by
      have : (regMean y - μ) ^ 2 > 0 := by
        have : regMean y - μ ≠ 0 := sub_ne_zero.2 (Ne.symm hμ)
        positivity
      positivity
    have e : (regSxx y + Fintype.card n * (regMean y - μ) ^ 2) / (2 * s) =
        regSxx y / (2 * s) + Fintype.card n * (regMean y - μ) ^ 2 / (2 * s) := by ring
    have e2 : ∑ i, (y i - regMean y) ^ 2 = regSxx y := rfl
    rw [e, e2]
    linarith
  · refine lt_of_le_of_lt hle ?_
    rw [hval, hval]
    exact neg_log_sub_div_lt hk hS hs hsn

/-! ### Expectation and positivity of the sum of squares -/

omit [DecidableEq n] in
/-- With equal variances Cochran's `Q` is the sum of squares divided by the variance. -/
theorem cochranQ_const_eq_regSxx [Nonempty n] {c : ℝ} (hc : c ≠ 0) (y : n → ℝ) :
    cochranQ (fun _ : n => c) y = regSxx y / c := by
  rw [cochranQ, ivwEstimate_equalVar hc, regSxx, Finset.sum_div]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [ivWeight]
  ring

omit [DecidableEq n] in
/-- **The expectations of the REML and ML variance estimates**: for square integrable, pairwise
uncorrelated observations with common mean `θ` and common variance `σ² > 0`, `n ≥ 2`,
`E[S/(n-1)] = σ²` and `E[S/n] = (n-1)/n · σ²`. Proof: `S/σ²` is Cochran's `Q` with equal
weights, of expectation `n - 1`. -/
theorem integral_regSxx_div [Nonempty n] {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
    [IsFiniteMeasure P] {Y : n → Ω → ℝ} {θ σ2 : ℝ} (hσ : 0 < σ2) (hn : 2 ≤ Fintype.card n)
    (hY : ∀ i, MemLp (Y i) 2 P) (hmean : ∀ i, ∫ ω, Y i ω ∂P = θ)
    (hvar : ∀ i, Var[Y i; P] = σ2) (hunc : ∀ i j, i ≠ j → cov[Y i, Y j; P] = 0) :
    ∫ ω, regSxx (fun i => Y i ω) / (Fintype.card n - 1) ∂P = σ2 ∧
      ∫ ω, regSxx (fun i => Y i ω) / Fintype.card n ∂P =
        (Fintype.card n - 1) / Fintype.card n * σ2 := by
  have hk : (0 : ℝ) < Fintype.card n := by exact_mod_cast Fintype.card_pos
  have hk1 : (0 : ℝ) < Fintype.card n - 1 := by
    have : (2 : ℝ) ≤ Fintype.card n := by exact_mod_cast hn
    linarith
  obtain ⟨-, hQ⟩ := integral_cochranQ (v := fun _ : n => σ2) (fun _ => hσ) hY hmean hvar hunc
  have hQ' : ∫ ω, regSxx (fun i => Y i ω) ∂P = (Fintype.card n - 1) * σ2 := by
    have e : ∀ ω, regSxx (fun i => Y i ω) = σ2 * cochranQ (fun _ : n => σ2) (fun i => Y i ω) :=
      fun ω => by rw [cochranQ_const_eq_regSxx hσ.ne']; field_simp
    simp_rw [e]
    rw [integral_const_mul, hQ]
    simp only [ivWeight, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    field_simp
  refine ⟨?_, ?_⟩
  · rw [integral_div, hQ']; field_simp
  · rw [integral_div, hQ']; field_simp

omit [DecidableEq n] in
/-- **The sum of squares is positive almost surely** under i.i.d. `N(θ, σ²)`, `σ² > 0`, with at
least two observations. Proof: `S = 0` forces `y a = y b` for two fixed indices, a proper linear
subspace, which is Lebesgue null, and the product law has a density. -/
theorem ae_regSxx_pos (θ : ℝ) {σ2 : ℝ} (hσ : 0 < σ2) {a b : n} (hab : a ≠ b) :
    ∀ᵐ y ∂(Measure.pi fun _ : n => gaussianReal θ σ2.toNNReal), 0 < regSxx y := by
  classical
  have hac : (Measure.pi fun _ : n => gaussianReal θ σ2.toNNReal) ≪ volume := by
    rw [← commonEffectKernel_apply (s := fun _ : n => σ2) (fun _ => hσ) θ, commonEffectKernel,
      Kernel.withDensity_apply _ (measurable_commonEffectLikelihood _), Kernel.const_apply,
      volume_pi]
    exact withDensity_absolutelyContinuous _ _
  set L : (n → ℝ) →ₗ[ℝ] ℝ :=
    LinearMap.proj (R := ℝ) (φ := fun _ : n => ℝ) a -
      LinearMap.proj (R := ℝ) (φ := fun _ : n => ℝ) b
  have hnull : volume (LinearMap.ker L : Set (n → ℝ)) = 0 := by
    refine Measure.addHaar_submodule _ _ fun h => ?_
    have hmem : (Pi.single a (1 : ℝ) : n → ℝ) ∈ LinearMap.ker L := by rw [h]; trivial
    simp only [LinearMap.mem_ker, L, LinearMap.sub_apply, LinearMap.proj_apply,
      Pi.single_eq_same, Pi.single_eq_of_ne hab.symm] at hmem
    norm_num at hmem
  refine Filter.mem_of_superset (hac (measure_mono_null (fun y hy => ?_) hnull))
    fun y hy => hy
  have hy' : regSxx y ≤ 0 := not_lt.1 hy
  have hz : regSxx y = 0 := le_antisymm hy' (Finset.sum_nonneg fun i _ => sq_nonneg _)
  have hall : ∀ i, y i - regMean y = 0 := by
    intro i
    have := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => sq_nonneg (y i - regMean y))).1 hz i
      (Finset.mem_univ _)
    exact pow_eq_zero_iff (two_ne_zero) |>.1 this
  change L y = 0
  simp only [L, LinearMap.sub_apply, LinearMap.proj_apply]
  linarith [hall a, hall b]

end MetaAnalysis

end CausalInference
