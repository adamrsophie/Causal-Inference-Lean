/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.PopulationAdjustment.CommonLimitLikelihood
public import Mathlib.Probability.Distributions.Gaussian.Real

/-!
# The normal linear model fitted by maximum likelihood is the least squares fit

The normal outcome model with the identity link specifies `y | c ~ N(z(c) ⬝ ξ, v)` with a known
variance `v ≠ 0`. Its likelihood is the likelihood `glmLikelihood` of a generalized linear model
with the normal density `gaussianPDFReal (z(c) ⬝ ξ) v y` (`commonLimitFollowUpGaussDens`), and it
is a strictly decreasing function of the residual sum of squares:

`∏ᵢ dens(z(cᵢ) ⬝ ξ, yᵢ) = (2πv)^{-n/2} exp(-RSS(ξ) / (2v))`
(`commonLimitFollowUpGauss_likelihood_eq`).

So the maximizers of the likelihood over all of `ℝ^κ` are the minimizers of the residual sum of
squares (`commonLimitFollowUpGauss_isMaxOn_iff`). The maximizer is unique exactly when the sample
design moment `Ĝ = n⁻¹ ∑ z(cᵢ) z(cᵢ)ᵀ` is invertible (`commonLimitFollowUpGauss_existsUnique_iff`),
and then it is the least
squares coefficient `Ĝ⁻¹ ĉ` (`commonLimitFollowUpGauss_isMaxOn_leastSquaresCoef`,
`commonLimitFollowUpGaussMLECoef_eq`). Every least squares theorem of the library is therefore a
theorem about the normal maximum likelihood fit on the events where `Ĝ` is invertible, which have
probability tending to one; `commonLimitFollowUpGauss_interaction_armMean` restates the common
limit of weighting and standardization for it.

**Why the consistency theorem for generalized linear models does not apply.**
`tendstoInMeasure_glmMLE` maximizes over a compact set and asks for the envelope
`|log dens(η, y)| ≤ a(y) + b |η|`. The normal log density
`-log √(2πv) - (y - η)² / (2v)` is quadratic in `η`, and no such envelope exists
(`commonLimitFollowUpGauss_not_envelope`). The identity with least squares closes this case
without the envelope and without a compact parameter set.

## Main definitions

* `commonLimitFollowUpGaussDens`: the normal density in the linear predictor.
* `commonLimitFollowUpGaussMLECoef`, `commonLimitFollowUpGaussMLE`: a maximizer of the normal
  likelihood over all coefficients.

## Main results

* `commonLimitFollowUpGauss_likelihood_eq`, `commonLimitFollowUpGauss_isMaxOn_iff`.
* `commonLimitFollowUpGauss_isMaxOn_leastSquaresCoef`, `commonLimitFollowUpGauss_existsUnique_iff`,
  `commonLimitFollowUpGaussMLECoef_eq`.
* `commonLimitFollowUpGauss_not_envelope`.
* `commonLimitFollowUpGauss_interaction_armMean`.

## References

* J. J. Caro and K. J. Ishak, *No head-to-head trial? Simulate the missing arms*,
  PharmacoEconomics 28 (2010).
-/

@[expose] public section

namespace CausalInference

namespace PopulationAdjustment

open MeasureTheory ProbabilityTheory Filter Topology Matrix EffectMeasure IndirectComparison
  PointTreatment Transport Real
open scoped NNReal

/-! ### Least squares algebra -/

section Algebra

variable {κ 𝒪 : Type*} [Fintype κ] [DecidableEq κ] {n : ℕ} {d : 𝒪 → κ → ℝ} {r : 𝒪 → ℝ}
  {x : Fin n → 𝒪}

omit [DecidableEq κ] in
/-- The sample design moment applied to `v`: `(Ĝ v)ⱼ = n⁻¹ ∑ᵢ dᵢⱼ (dᵢ ⬝ v)`. -/
theorem commonLimitFollowUpGauss_fitGram_mulVec (v : κ → ℝ) (j : κ) :
    (fitGram d x *ᵥ v) j = (n : ℝ)⁻¹ * ∑ i, d (x i) j * (d (x i) ⬝ᵥ v) := by
  simp only [fitGram, mulVec, dotProduct, Matrix.of_apply, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => by ring

omit [DecidableEq κ] in
/-- The quadratic form of the sample design moment: `vᵀ Ĝ v = n⁻¹ ∑ᵢ (dᵢ ⬝ v)²`. -/
theorem commonLimitFollowUpGauss_quadForm (v : κ → ℝ) :
    v ⬝ᵥ (fitGram d x *ᵥ v) = (n : ℝ)⁻¹ * ∑ i, (d (x i) ⬝ᵥ v) ^ 2 := by
  simp only [dotProduct, commonLimitFollowUpGauss_fitGram_mulVec, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [sq, Finset.mul_sum, Finset.sum_mul]
  exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => by ring

/-- **The residual sum of squares around the least squares coefficient**: when `Ĝ` is
invertible, `RSS(ξ) = RSS(β̂) + ∑ᵢ (dᵢ ⬝ (ξ - β̂))²`. -/
theorem commonLimitFollowUpGauss_rss_eq (h : (fitGram d x).det ≠ 0) (ξ : κ → ℝ) :
    ∑ i, (r (x i) - d (x i) ⬝ᵥ ξ) ^ 2 =
      ∑ i, (r (x i) - d (x i) ⬝ᵥ leastSquaresCoef d r x) ^ 2 +
        ∑ i, (d (x i) ⬝ᵥ (ξ - leastSquaresCoef d r x)) ^ 2 := by
  set β := leastSquaresCoef d r x
  have hne := fitGram_mulVec_leastSquaresCoef r h
  have hj : ∀ j, ∑ i, d (x i) j * (r (x i) - d (x i) ⬝ᵥ β) = 0 := by
    intro j
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn
      simp
    have e := congrFun hne j
    rw [commonLimitFollowUpGauss_fitGram_mulVec] at e
    simp only [fitCross] at e
    have hn' : (n : ℝ)⁻¹ ≠ 0 := inv_ne_zero (Nat.cast_ne_zero.2 hn.ne')
    have e' := mul_left_cancel₀ hn' e
    simp only [mul_sub, Finset.sum_sub_distrib]
    rw [e', sub_self]
  set v := ξ - β
  have horth : ∑ i, (r (x i) - d (x i) ⬝ᵥ β) * (d (x i) ⬝ᵥ v) = 0 := by
    have : ∑ i, (r (x i) - d (x i) ⬝ᵥ β) * (d (x i) ⬝ᵥ v) =
        ∑ k, v k * ∑ i, d (x i) k * (r (x i) - d (x i) ⬝ᵥ β) := by
      simp only [dotProduct, Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun i _ => ?_
      ring
    rw [this]
    simp [hj]
  have hsq : ∀ i, (r (x i) - d (x i) ⬝ᵥ ξ) ^ 2 = (r (x i) - d (x i) ⬝ᵥ β) ^ 2 -
      2 * ((r (x i) - d (x i) ⬝ᵥ β) * (d (x i) ⬝ᵥ v)) + (d (x i) ⬝ᵥ v) ^ 2 := fun i => by
    rw [show d (x i) ⬝ᵥ v = d (x i) ⬝ᵥ ξ - d (x i) ⬝ᵥ β from dotProduct_sub _ _ _]
    ring
  simp only [hsq, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, horth]
  ring

end Algebra

/-! ### The normal likelihood -/

section Likelihood

variable {C κ : Type*} [Fintype κ] [DecidableEq κ]

/-- The **normal density** `N(η, v)` at `y`, as a function of the linear predictor `η`: the
outcome density of the normal linear model with the identity link and variance `v`. -/
noncomputable def commonLimitFollowUpGaussDens (v : ℝ≥0) (η y : ℝ) : ℝ :=
  gaussianPDFReal η v y

/-- The residual sum of squares `∑ᵢ (yᵢ - z(cᵢ) ⬝ ξ)²` of a data vector of records `(c, y)`. -/
noncomputable def commonLimitFollowUpGaussRSS (z : C → κ → ℝ) {n : ℕ} (x : Fin n → C × ℝ)
    (ξ : κ → ℝ) : ℝ :=
  ∑ i, ((x i).2 - z (x i).1 ⬝ᵥ ξ) ^ 2

omit [DecidableEq κ] in
/-- **The normal likelihood is a decreasing function of the residual sum of squares** for a
variance `v ≠ 0`:
`∏ᵢ dens(z(cᵢ) ⬝ ξ, yᵢ) = (√(2πv))⁻ⁿ exp(-RSS(ξ) / (2v))`. -/
theorem commonLimitFollowUpGauss_likelihood_eq {v : ℝ≥0} (_hv : v ≠ 0) (z : C → κ → ℝ)
    {n : ℕ} (x : Fin n → C × ℝ) (ξ : κ → ℝ) :
    glmLikelihood (commonLimitFollowUpGaussDens v) z x ξ =
      (√(2 * π * v))⁻¹ ^ n * Real.exp (-commonLimitFollowUpGaussRSS z x ξ / (2 * v)) := by
  simp only [glmLikelihood, commonLimitFollowUpGaussDens, gaussianPDFReal,
    commonLimitFollowUpGaussRSS]
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
    ← Real.exp_sum]
  congr 2
  simp only [neg_div, Finset.sum_neg_distrib, Finset.sum_div]

omit [DecidableEq κ] in
/-- **Maximum likelihood is least squares**: for a variance `v ≠ 0`, `ξ` maximizes the normal
likelihood over all coefficients exactly when it minimizes the residual sum of squares. -/
theorem commonLimitFollowUpGauss_isMaxOn_iff {v : ℝ≥0} (hv : v ≠ 0) (z : C → κ → ℝ) {n : ℕ}
    (x : Fin n → C × ℝ) (ξ : κ → ℝ) :
    IsMaxOn (glmLikelihood (commonLimitFollowUpGaussDens v) z x) Set.univ ξ ↔
      IsMinOn (commonLimitFollowUpGaussRSS z x) Set.univ ξ := by
  have hv0 : (0 : ℝ) < v := lt_of_le_of_ne v.2 (by exact_mod_cast hv.symm)
  have hK : 0 < (√(2 * π * v))⁻¹ ^ n := by positivity
  have hle : ∀ ξ' : κ → ℝ, glmLikelihood (commonLimitFollowUpGaussDens v) z x ξ' ≤
      glmLikelihood (commonLimitFollowUpGaussDens v) z x ξ ↔
        commonLimitFollowUpGaussRSS z x ξ ≤ commonLimitFollowUpGaussRSS z x ξ' := fun ξ' => by
    rw [commonLimitFollowUpGauss_likelihood_eq hv, commonLimitFollowUpGauss_likelihood_eq hv,
      mul_le_mul_iff_right₀ hK, Real.exp_le_exp, div_le_div_iff_of_pos_right (by positivity),
      neg_le_neg_iff]
  rw [isMaxOn_iff, isMinOn_iff]
  exact forall_congr' fun ξ' => imp_congr_right fun _ => hle ξ'

omit [DecidableEq κ] in
/-- The residual sum of squares of the records is the least squares criterion of the design
`d(c, y) = z(c)` and the response `r(c, y) = y`. -/
theorem commonLimitFollowUpGauss_rss_eq_sum (z : C → κ → ℝ) {n : ℕ} (x : Fin n → C × ℝ)
    (ξ : κ → ℝ) : commonLimitFollowUpGaussRSS z x ξ =
      ∑ i, (Prod.snd (x i) - (fun q : C × ℝ => z q.1) (x i) ⬝ᵥ ξ) ^ 2 := rfl

/-- **The least squares coefficient maximizes the normal likelihood, and is its only maximizer,
when the sample design moment is invertible.** -/
theorem commonLimitFollowUpGauss_isMaxOn_leastSquaresCoef {v : ℝ≥0} (hv : v ≠ 0)
    (z : C → κ → ℝ) {n : ℕ} (x : Fin n → C × ℝ)
    (h : (fitGram (fun q : C × ℝ => z q.1) x).det ≠ 0) :
    IsMaxOn (glmLikelihood (commonLimitFollowUpGaussDens v) z x) Set.univ
        (leastSquaresCoef (fun q : C × ℝ => z q.1) Prod.snd x) ∧
      ∀ ξ, IsMaxOn (glmLikelihood (commonLimitFollowUpGaussDens v) z x) Set.univ ξ →
        ξ = leastSquaresCoef (fun q : C × ℝ => z q.1) Prod.snd x := by
  set β := leastSquaresCoef (fun q : C × ℝ => z q.1) Prod.snd x
  refine ⟨(commonLimitFollowUpGauss_isMaxOn_iff hv z x β).2 fun ξ _ => ?_, fun ξ hξ => ?_⟩
  · change commonLimitFollowUpGaussRSS z x β ≤ commonLimitFollowUpGaussRSS z x ξ
    rw [commonLimitFollowUpGauss_rss_eq_sum, commonLimitFollowUpGauss_rss_eq_sum,
      commonLimitFollowUpGauss_rss_eq h ξ]
    have : 0 ≤ ∑ i, ((fun q : C × ℝ => z q.1) (x i) ⬝ᵥ (ξ - β)) ^ 2 :=
      Finset.sum_nonneg fun i _ => sq_nonneg _
    linarith
  · have hmin := (commonLimitFollowUpGauss_isMaxOn_iff hv z x ξ).1 hξ (Set.mem_univ β)
    change commonLimitFollowUpGaussRSS z x ξ ≤ commonLimitFollowUpGaussRSS z x β at hmin
    rw [commonLimitFollowUpGauss_rss_eq_sum, commonLimitFollowUpGauss_rss_eq_sum,
      commonLimitFollowUpGauss_rss_eq h ξ] at hmin
    have hnn : ∀ i ∈ Finset.univ, 0 ≤ ((fun q : C × ℝ => z q.1) (x i) ⬝ᵥ (ξ - β)) ^ 2 :=
      fun i _ => sq_nonneg _
    have h0 : ∑ i, ((fun q : C × ℝ => z q.1) (x i) ⬝ᵥ (ξ - β)) ^ 2 = 0 :=
      le_antisymm (by linarith) (Finset.sum_nonneg hnn)
    have hi := (Finset.sum_eq_zero_iff_of_nonneg hnn).1 h0
    have hG : fitGram (fun q : C × ℝ => z q.1) x *ᵥ (ξ - β) = 0 := by
      funext j
      rw [commonLimitFollowUpGauss_fitGram_mulVec]
      simp [fun i => pow_eq_zero_iff (n := 2) two_ne_zero |>.1 (hi i (Finset.mem_univ i))]
    exact sub_eq_zero.1 (eq_zero_of_mulVec_eq_zero h hG)

/-- **The maximizer of the normal likelihood is unique exactly when the sample design moment is
invertible.** For `v ≠ 0`: if `Ĝ` is singular, a nonzero `u` with `Ĝ u = 0` has `z(cᵢ) ⬝ u = 0`
for every record, and every maximizer `ξ` comes with a second one `ξ + u`. -/
theorem commonLimitFollowUpGauss_existsUnique_iff {v : ℝ≥0} (hv : v ≠ 0) (z : C → κ → ℝ)
    {n : ℕ} (x : Fin n → C × ℝ) :
    (∃! ξ, IsMaxOn (glmLikelihood (commonLimitFollowUpGaussDens v) z x) Set.univ ξ) ↔
      (fitGram (fun q : C × ℝ => z q.1) x).det ≠ 0 := by
  constructor
  · rintro ⟨ξ, hξ, huniq⟩ hdet
    obtain ⟨u, hu0, hu⟩ := (exists_mulVec_eq_zero_iff (M := fitGram (fun q : C × ℝ => z q.1)
      x)).2 hdet
    have hq := commonLimitFollowUpGauss_quadForm (d := fun q : C × ℝ => z q.1) (x := x) u
    rw [hu, dotProduct_zero] at hq
    have hzero : ∀ i, z (x i).1 ⬝ᵥ u = 0 := fun i => by
      have hn : (n : ℝ)⁻¹ ≠ 0 := inv_ne_zero (Nat.cast_ne_zero.2 (Fin.pos i).ne')
      have hs : ∑ i, ((fun q : C × ℝ => z q.1) (x i) ⬝ᵥ u) ^ 2 = 0 :=
        (mul_eq_zero.1 hq.symm).resolve_left hn
      have := (Finset.sum_eq_zero_iff_of_nonneg fun i _ => sq_nonneg _).1 hs i
        (Finset.mem_univ i)
      exact pow_eq_zero_iff two_ne_zero |>.1 this
    have hrss : ∀ η, commonLimitFollowUpGaussRSS z x (η + u) =
        commonLimitFollowUpGaussRSS z x η := fun η => by
      simp only [commonLimitFollowUpGaussRSS, dotProduct_add, hzero, add_zero]
    have hξu : IsMaxOn (glmLikelihood (commonLimitFollowUpGaussDens v) z x) Set.univ
        (ξ + u) := by
      rw [commonLimitFollowUpGauss_isMaxOn_iff hv] at hξ ⊢
      intro η hη
      change commonLimitFollowUpGaussRSS z x (ξ + u) ≤ commonLimitFollowUpGaussRSS z x η
      rw [hrss]
      exact hξ hη
    have := huniq _ hξu
    exact hu0 (by simpa using this)
  · intro h
    obtain ⟨hmax, huniq⟩ := commonLimitFollowUpGauss_isMaxOn_leastSquaresCoef hv z x h
    exact ⟨_, hmax, huniq⟩

/-- The **normal maximum likelihood coefficient** of a data vector: a maximizer of the normal
likelihood over all coefficients when one exists, and `0` otherwise. -/
noncomputable def commonLimitFollowUpGaussMLECoef (v : ℝ≥0) (z : C → κ → ℝ) {n : ℕ}
    (x : Fin n → C × ℝ) : κ → ℝ :=
  open Classical in
  if h : ∃ ξ, IsMaxOn (glmLikelihood (commonLimitFollowUpGaussDens v) z x) Set.univ ξ then
    h.choose else 0

/-- **The normal maximum likelihood coefficient is the least squares coefficient** when the
sample design moment is invertible. -/
theorem commonLimitFollowUpGaussMLECoef_eq {v : ℝ≥0} (hv : v ≠ 0) (z : C → κ → ℝ) {n : ℕ}
    (x : Fin n → C × ℝ) (h : (fitGram (fun q : C × ℝ => z q.1) x).det ≠ 0) :
    commonLimitFollowUpGaussMLECoef v z x =
      leastSquaresCoef (fun q : C × ℝ => z q.1) Prod.snd x := by
  obtain ⟨hmax, huniq⟩ := commonLimitFollowUpGauss_isMaxOn_leastSquaresCoef hv z x h
  have hex : ∃ ξ, IsMaxOn (glmLikelihood (commonLimitFollowUpGaussDens v) z x) Set.univ ξ :=
    ⟨_, hmax⟩
  rw [commonLimitFollowUpGaussMLECoef]
  split_ifs
  exact huniq _ hex.choose_spec

/-- **No envelope linear in the predictor bounds the normal log density.** For `v ≠ 0` there are
no `a` and `b` with `|log dens(η, y)| ≤ a(y) + b |η|` for all `η` and `y`: at `y = 0` the log
density is `-log √(2πv) - η² / (2v)`, quadratic in `η`. This is the envelope condition of
`tendstoInMeasure_glmMLE`. -/
theorem commonLimitFollowUpGauss_not_envelope {v : ℝ≥0} (hv : v ≠ 0) :
    ¬ ∃ (a : ℝ → ℝ) (b : ℝ), ∀ η y,
      |Real.log (commonLimitFollowUpGaussDens v η y)| ≤ a y + b * |η| := by
  rintro ⟨a, b, h⟩
  have hv0 : (0 : ℝ) < v := lt_of_le_of_ne v.2 (by exact_mod_cast hv.symm)
  set L := Real.log (√(2 * π * v))
  have hlog : ∀ η, Real.log (commonLimitFollowUpGaussDens v η 0) = -L - η ^ 2 / (2 * v) :=
    fun η => by
      rw [commonLimitFollowUpGaussDens, gaussianPDFReal, Real.log_mul (by positivity)
        (Real.exp_pos _).ne', Real.log_inv, Real.log_exp]
      ring
  set A := |a 0| + |L| + 1
  set η := 2 * v * (|b| + A) + 1
  have hη1 : 1 ≤ η := by
    have : 0 ≤ 2 * (v : ℝ) * (|b| + A) := by positivity
    linarith
  have hη0 : 0 < η := by linarith
  have hq : η ^ 2 / (2 * v) ≥ η * (|b| + A) := by
    rw [ge_iff_le, le_div_iff₀ (by positivity)]
    have : 2 * (v : ℝ) * (|b| + A) ≤ η := by linarith
    nlinarith [abs_nonneg b, abs_nonneg (a 0), abs_nonneg L]
  have h1 := h η 0
  rw [hlog, abs_of_pos hη0] at h1
  have h2 : L + η ^ 2 / (2 * v) ≤ |-L - η ^ 2 / (2 * v)| := by
    rw [show L + η ^ 2 / (2 * v) = -(-L - η ^ 2 / (2 * v)) by ring]
    exact neg_le_abs _
  have hbη : b * η ≤ |b| * η := mul_le_mul_of_nonneg_right (le_abs_self b) hη0.le
  have hA : A ≤ η * A := le_mul_of_one_le_left (by positivity) hη1
  have hL : -|L| ≤ L := neg_abs_le L
  have ha : a 0 ≤ |a 0| := le_abs_self _
  nlinarith

end Likelihood

/-! ### The common limit with the normal maximum likelihood fit -/

section CommonLimit

variable {Ω₁ Ω₂ Ξ 𝒳 ι : Type*} [MeasurableSpace Ω₁] [MeasurableSpace Ω₂] [MeasurableSpace Ξ]
  [MeasurableSpace 𝒳] {p : ℕ} {T : Trial Ω₁ 𝒳 Bool} {Q : Population Ω₂ 𝒳 ι} {P : Measure Ξ}
  {O : ℕ → Ξ → 𝒳 × Bool × ℝ} {φ : 𝒳 → Fin p → ℝ} {t : Fin p → ℝ}
  {ξ₀ : Option (Fin p) ⊕ Option (Fin p) → ℝ}

/-- The record `((x, a), y)` of the normal likelihood fit of a trial record `(x, a, y)`. -/
def commonLimitFollowUpGaussRecord (o : 𝒳 × Bool × ℝ) : (𝒳 × Bool) × ℝ := ((o.1, o.2.1), o.2.2)

/-- The **normal maximum likelihood fit** of the interaction design from the first `n` records
of a sample. -/
noncomputable def commonLimitFollowUpGaussMLE (v : ℝ≥0) (φ : 𝒳 → Fin p → ℝ)
    (O : ℕ → Ξ → 𝒳 × Bool × ℝ) (n : ℕ) (ω : Ξ) : Option (Fin p) ⊕ Option (Fin p) → ℝ :=
  commonLimitFollowUpGaussMLECoef v (fun c : 𝒳 × Bool => featureInteractionDesign φ c.2 c.1)
    (fun i : Fin n => commonLimitFollowUpGaussRecord (O i ω))

/-- **The common limit with the normal maximum likelihood fit.** Under the hypotheses of
`commonLimit_interaction_armMean`, and for any variance `v ≠ 0` of the normal working model
(the true outcome law need not be normal), the weighted arm mean and the standardized normal
maximum likelihood fit `∫ z(a, x)ᵀξ̂_ML dQ_X` both converge in probability to `E_Q[Y(s)]`, and
their difference converges in probability to `0`. The fit equals the least squares fit on the
events where the sample design moment is invertible, whose probability tends to one. -/
theorem commonLimitFollowUpGauss_interaction_armMean [IsProbabilityMeasure T.μ]
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q.μ] {v : ℝ≥0} (hv : v ≠ 0)
    (hT : T.IsRandomizedTwoArm) (hY2 : ∀ a, MemLp (T.Y a) 2 T.μ)
    (hφ : Measurable φ) {B : ℝ} (hB : ∀ x, ‖φ x - t‖ ≤ B) {δ : ℝ} (hδ : 0 < δ)
    (hmargin : ∀ v : Fin p → ℝ, ‖v‖ = 1 → δ ≤ T.covLaw.real {x | δ ≤ v ⬝ᵥ (φ x - t)})
    (hreg : IsOutcomeRegression T.μ T.A T.X T.obsOutcome
      fun a x => featureInteractionDesign φ a x ⬝ᵥ ξ₀)
    {σ2 : ℝ} (hvar : T.ipdLaw[fun o => (o.2.2 - featureInteractionDesign φ o.2.1 o.1 ⬝ᵥ ξ₀) ^ 2 |
      MeasurableSpace.comap (fun o : 𝒳 × Bool × ℝ => (o.1, o.2.1)) inferInstance]
        ≤ᵐ[T.ipdLaw] fun _ => σ2)
    (hO : IsIIDSample O P) (hOm : ∀ i, Measurable (O i)) (hlaw : P.map (O 0) = T.ipdLaw)
    (hX₂ : Measurable Q.X) (ht : ∀ k, ∫ x, φ x k ∂Q.covLaw = t k) (a : Bool) {s : ι}
    (hYQ : Integrable (Q.Y s) Q.μ)
    (hsi : StructurallyInvariant T.μ T.X (T.Y a) Q.μ Q.X (Q.Y s)) (hov : Q.covLaw ≪ T.covLaw) :
    IsConsistent (sampleBalancedArmMean φ t O a) (Q.armMean s) P ∧
      TendstoInMeasure P (fun n ω => ∫ x, featureInteractionDesign φ a x ⬝ᵥ
        commonLimitFollowUpGaussMLE v φ O n ω ∂Q.covLaw) atTop (fun _ => Q.armMean s) ∧
      TendstoInMeasure P (fun n ω => ∫ x, featureInteractionDesign φ a x ⬝ᵥ
        commonLimitFollowUpGaussMLE v φ O n ω ∂Q.covLaw - sampleBalancedArmMean φ t O a n ω)
        atTop (fun _ => 0) := by
  obtain ⟨hW, hS, -⟩ := commonLimit_interaction_armMean hT hY2 hφ hB hδ hmargin hreg hvar hO hOm
    hlaw hX₂ ht a hYQ hsi hov
  have hM := T.linearOutcomeModel_featureInteraction hT hY2 hφ hB hδ hmargin hreg
  -- the sample design moment is invertible with probability tending to one
  have hYo : Measurable T.obsOutcome :=
    measurable_obsOutcome (A := T.A) (Y := T.Y) hT.measurable_A hT.measurable_Y
  have hD : Measurable fun ω => (T.X ω, T.A ω, T.obsOutcome ω) :=
    hT.measurable_X.prodMk (hT.measurable_A.prodMk hYo)
  set z := featureInteractionDesign φ
  have hdm := measurable_recordDesign hM.measurable_z
  have hzA : ∀ j, MemLp (fun ω => z (T.A ω) (T.X ω) j) 2 T.μ := fun j =>
    memLp_two_select (f := fun a ω => z a (T.X ω) j) hT.measurable_A
      (fun a => (hM.measurable_z a j).comp hT.measurable_X) fun a => hM.memLp_z a j
  have hd2 : ∀ j, MemLp (fun o => recordDesign z o j) 2 (P.map (O 0)) := fun j => by
    rw [hlaw, Trial.ipdLaw, memLp_map_measure_iff (hdm j).aestronglyMeasurable hD.aemeasurable]
    exact hzA j
  have hGμ : ∀ j k, ∫ o, recordDesign z o j * recordDesign z o k ∂(P.map (O 0)) =
      ∫ ω, z (T.A ω) (T.X ω) j * z (T.A ω) (T.X ω) k ∂T.μ := fun j k => by
    rw [hlaw, Trial.ipdLaw, integral_map (f := fun o => recordDesign z o j * recordDesign z o k)
      hD.aemeasurable ((hdm j).mul (hdm k)).aestronglyMeasurable]
    rfl
  have hG' : (Matrix.of fun j k => ∫ o, recordDesign z o j * recordDesign z o k
      ∂(P.map (O 0))).PosDef := by
    simp only [hGμ]; exact hM.posDef
  have hev := withProbTendingToOne_det_fitGram_ne_zero hO hdm hd2 hG'
  -- on these events the normal fit is the least squares fit
  have hagree : ∀ n, ∀ ω ∈ {ω | (fitGram (recordDesign z) (fun i : Fin n => O i ω)).det ≠ 0},
      ∫ x, z a x ⬝ᵥ leastSquaresFit (recordDesign z) recordResponse O n ω ∂Q.covLaw =
        ∫ x, z a x ⬝ᵥ commonLimitFollowUpGaussMLE v φ O n ω ∂Q.covLaw := fun n ω hω => by
    rw [commonLimitFollowUpGaussMLE, commonLimitFollowUpGaussMLECoef_eq hv _ _ hω]
    rfl
  have hS' := hS.congr_withProbTendingToOne hev hagree
  exact ⟨hW, hS', tendstoInMeasure_sub_zero_of_same_limit hS' hW⟩

end CommonLimit

end PopulationAdjustment

end CausalInference
