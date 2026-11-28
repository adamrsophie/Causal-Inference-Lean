/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.PointTreatment.SampleEstimators
public import CausalInference.Estimation.LawOfLargeNumbers
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.MeasureTheory.Function.L2Space

/-!
# The least squares fit of a linear outcome model

An outcome model with a linear predictor is fitted to the individual data of a trial by least
squares. A record `o` has a design row `d(o) ∈ ℝ^κ` (for a trial record `(x, a, y)` a function
of the covariates and the arm) and a response `r(o)` (the outcome). From the first `n` records
the fit is

`β̂_n = Ĝ_n⁻¹ ĉ_n`, `Ĝ_n = n⁻¹ ∑ d(o_i) d(o_i)ᵀ`, `ĉ_n = n⁻¹ ∑ d(o_i) r(o_i)`,

with Mathlib's total matrix inverse (`Ĝ_n⁻¹ = 0` when `Ĝ_n` is singular). The estimator is a
function of the data vector (`leastSquaresCoef`) evaluated at the sample (`leastSquaresFit`).

* **It is the least squares solution where that is meaningful**: when `det Ĝ_n ≠ 0` the fit
  solves the normal equations (`fitGram_mulVec_leastSquaresCoef`) and minimizes the residual sum
  of squares (`sum_sq_leastSquaresCoef_le`).
* **The sample design is invertible with probability tending to one**
  (`withProbTendingToOne_det_fitGram_ne_zero`) when the population design second moment
  `G = E[d dᵀ]` is positive definite and the design has finite second moments.
* **Consistency for the projection coefficient** (`tendstoInMeasure_leastSquaresFit`): with
  finite second moments of the design and the response and `G` positive definite, `β̂_n`
  converges in probability to `G⁻¹ E[d r]`, with no model assumed.
* **Consistency for the regression coefficient** (`gram_mulVec_eq_cross_of_condExp`,
  `tendstoInMeasure_leastSquaresFit_of_isOutcomeRegression`): if the regression of the outcome
  on the covariates and the arm is linear, `E[Y | X, A] = z(A, X)ᵀξ₀`
  (`PointTreatment.IsOutcomeRegression`), the normal equations hold at `ξ₀` and `β̂_n → ξ₀`.
* **Positive definiteness from the design** (`posDef_gram_of_ae`): `G` is positive definite as
  soon as no nonzero `v` has `d ⬝ v = 0` almost surely; `dotProduct_gram_mulVec` gives
  `vᵀ G v = E[(d ⬝ v)²]`.

## Main definitions

* `fitGram`, `fitCross`, `leastSquaresCoef`: the sample design moments and the least squares
  coefficient of a data vector.
* `leastSquaresFit`: the least squares coefficient of the first `n` records of a sample.

## Main results

* `fitGram_mulVec_leastSquaresCoef`, `sum_sq_leastSquaresCoef_le`.
* `tendstoInMeasure_fitGram`, `tendstoInMeasure_fitCross`,
  `withProbTendingToOne_det_fitGram_ne_zero`, `tendstoInMeasure_leastSquaresFit`.
* `dotProduct_gram_mulVec`, `posDef_gram_of_ae`.
* `gram_mulVec_eq_cross_of_condExp`, `tendstoInMeasure_leastSquaresFit_of_isOutcomeRegression`.

## References

* A. W. van der Vaart (1998), *Asymptotic Statistics*, chapter 5.
-/

@[expose] public section

namespace CausalInference

namespace PopulationAdjustment

open MeasureTheory ProbabilityTheory Filter Topology Matrix PointTreatment
open scoped ENNReal

/-! ### The estimator as a function of the data -/

section Data

variable {κ 𝒪 : Type*} [Fintype κ] [DecidableEq κ]

/-- The **sample design second moment** `n⁻¹ ∑ᵢ d(xᵢ) d(xᵢ)ᵀ` of a data vector `x`. -/
noncomputable def fitGram {n : ℕ} (d : 𝒪 → κ → ℝ) (x : Fin n → 𝒪) : Matrix κ κ ℝ :=
  Matrix.of fun j k => (n : ℝ)⁻¹ * ∑ i, d (x i) j * d (x i) k

/-- The **sample design response moment** `n⁻¹ ∑ᵢ d(xᵢ) r(xᵢ)` of a data vector `x`. -/
noncomputable def fitCross {n : ℕ} (d : 𝒪 → κ → ℝ) (r : 𝒪 → ℝ) (x : Fin n → 𝒪) : κ → ℝ :=
  fun j => (n : ℝ)⁻¹ * ∑ i, d (x i) j * r (x i)

/-- The **least squares coefficient** `Ĝ⁻¹ ĉ` of a data vector, with the total matrix inverse
(`Ĝ⁻¹ = 0` for a singular `Ĝ`). -/
noncomputable def leastSquaresCoef {n : ℕ} (d : 𝒪 → κ → ℝ) (r : 𝒪 → ℝ) (x : Fin n → 𝒪) :
    κ → ℝ :=
  (fitGram d x)⁻¹ *ᵥ fitCross d r x

/-- **The normal equations.** When the sample design moment is invertible, the least squares
coefficient solves `Ĝ β = ĉ`. -/
theorem fitGram_mulVec_leastSquaresCoef {n : ℕ} {d : 𝒪 → κ → ℝ} (r : 𝒪 → ℝ) {x : Fin n → 𝒪}
    (h : (fitGram d x).det ≠ 0) : fitGram d x *ᵥ leastSquaresCoef d r x = fitCross d r x := by
  rw [leastSquaresCoef, mulVec_mulVec, mul_nonsing_inv _ (isUnit_iff_ne_zero.2 h), one_mulVec]

/-- **The least squares coefficient minimizes the residual sum of squares** when the sample
design moment is invertible: `∑ᵢ (rᵢ - dᵢ ⬝ β̂)² ≤ ∑ᵢ (rᵢ - dᵢ ⬝ ξ)²` for every `ξ`. The
residuals are orthogonal to the design by the normal equations. -/
theorem sum_sq_leastSquaresCoef_le {n : ℕ} {d : 𝒪 → κ → ℝ} {r : 𝒪 → ℝ} {x : Fin n → 𝒪}
    (h : (fitGram d x).det ≠ 0) (ξ : κ → ℝ) :
    ∑ i, (r (x i) - d (x i) ⬝ᵥ leastSquaresCoef d r x) ^ 2 ≤
      ∑ i, (r (x i) - d (x i) ⬝ᵥ ξ) ^ 2 := by
  set β := leastSquaresCoef d r x
  have hne := fitGram_mulVec_leastSquaresCoef r h
  have hj : ∀ j, ∑ i, d (x i) j * (r (x i) - d (x i) ⬝ᵥ β) = 0 := by
    intro j
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn
      simp
    have e := congrFun hne j
    have e' : ∑ k, (n : ℝ)⁻¹ * (∑ i, d (x i) j * d (x i) k) * β k =
        (n : ℝ)⁻¹ * ∑ i, d (x i) j * (d (x i) ⬝ᵥ β) := by
      simp only [dotProduct, Finset.mul_sum, Finset.sum_mul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => ?_
      ring
    simp only [fitGram, fitCross, mulVec, dotProduct, Matrix.of_apply] at e
    have hn' : (n : ℝ)⁻¹ ≠ 0 := inv_ne_zero (Nat.cast_ne_zero.2 hn.ne')
    have e'' : ∑ i, d (x i) j * (d (x i) ⬝ᵥ β) = ∑ i, d (x i) j * r (x i) := by
      have := e'.symm.trans e
      exact mul_left_cancel₀ hn' this
    simp only [mul_sub, Finset.sum_sub_distrib, e'', sub_self]
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
  have h0 : 0 ≤ ∑ i, (d (x i) ⬝ᵥ v) ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
  linarith

end Data

/-! ### The estimator on a sample -/

section Sample

variable {κ 𝒪 Ω : Type*} [Fintype κ] [DecidableEq κ] [MeasurableSpace 𝒪] [MeasurableSpace Ω]

/-- The **least squares fit** from the first `n` records `O 0, …, O (n - 1)` of a sample: the
least squares coefficient of the data vector. -/
noncomputable def leastSquaresFit (d : 𝒪 → κ → ℝ) (r : 𝒪 → ℝ) (O : ℕ → Ω → 𝒪) (n : ℕ)
    (ω : Ω) : κ → ℝ :=
  leastSquaresCoef d r (fun i : Fin n => O i ω)

omit [Fintype κ] [DecidableEq κ] [MeasurableSpace 𝒪] [MeasurableSpace Ω] in
/-- The entries of the sample design moment are sample means. -/
theorem fitGram_sample (d : 𝒪 → κ → ℝ) (O : ℕ → Ω → 𝒪) (n : ℕ) (ω : Ω) (j k : κ) :
    fitGram d (fun i : Fin n => O i ω) j k = sampleMean (fun o => d o j * d o k) O n ω := by
  simp [fitGram, sampleMean, Finset.sum_range]

omit [Fintype κ] [DecidableEq κ] [MeasurableSpace 𝒪] [MeasurableSpace Ω] in
/-- The entries of the sample design response moment are sample means. -/
theorem fitCross_sample (d : 𝒪 → κ → ℝ) (r : 𝒪 → ℝ) (O : ℕ → Ω → 𝒪) (n : ℕ) (ω : Ω) (j : κ) :
    fitCross d r (fun i : Fin n => O i ω) j = sampleMean (fun o => d o j * r o) O n ω := by
  simp [fitCross, sampleMean, Finset.sum_range]

variable {P : Measure Ω} [IsProbabilityMeasure P] {O : ℕ → Ω → 𝒪}

omit [DecidableEq κ] in
/-- **The sample design moment converges** in probability to the population design second
moment `E[d dᵀ]`, for design coordinates with finite second moments. -/
theorem tendstoInMeasure_fitGram (hO : IsIIDSample O P) {d : 𝒪 → κ → ℝ}
    (hd : ∀ j, Measurable fun o => d o j) (hd2 : ∀ j, MemLp (fun o => d o j) 2 (P.map (O 0))) :
    TendstoInMeasure P (fun n ω j k => fitGram d (fun i : Fin n => O i ω) j k) atTop
      (fun _ j k => ∫ o, d o j * d o k ∂(P.map (O 0))) := by
  refine tendstoInMeasure_pi (X := fun j n ω k => fitGram d (fun i : Fin n => O i ω) j k)
    fun j => tendstoInMeasure_pi (X := fun k n ω => fitGram d (fun i : Fin n => O i ω) j k)
      fun k => ?_
  have hf : Measurable fun o => d o j * d o k := (hd j).mul (hd k)
  have hint : Integrable (fun o => d o j * d o k) (P.map (O 0)) :=
    (hd2 j).integrable_mul (hd2 k)
  have h := sampleMean_isConsistent hO hf
    ((integrable_map_measure hf.aestronglyMeasurable (hO.aemeasurable 0)).1 hint)
  rw [IsConsistent, ← integral_map (hO.aemeasurable 0) hf.aestronglyMeasurable] at h
  simpa only [fitGram_sample] using h

omit [DecidableEq κ] in
/-- **The sample design response moment converges** in probability to `E[d r]`, for a design and
a response with finite second moments. -/
theorem tendstoInMeasure_fitCross (hO : IsIIDSample O P) {d : 𝒪 → κ → ℝ} {r : 𝒪 → ℝ}
    (hd : ∀ j, Measurable fun o => d o j) (hr : Measurable r)
    (hd2 : ∀ j, MemLp (fun o => d o j) 2 (P.map (O 0))) (hr2 : MemLp r 2 (P.map (O 0))) :
    TendstoInMeasure P (fun n ω j => fitCross d r (fun i : Fin n => O i ω) j) atTop
      (fun _ j => ∫ o, d o j * r o ∂(P.map (O 0))) := by
  refine tendstoInMeasure_pi (X := fun j n ω => fitCross d r (fun i : Fin n => O i ω) j)
    fun j => ?_
  have hf : Measurable fun o => d o j * r o := (hd j).mul hr
  have hint : Integrable (fun o => d o j * r o) (P.map (O 0)) := (hd2 j).integrable_mul hr2
  have h := sampleMean_isConsistent hO hf
    ((integrable_map_measure hf.aestronglyMeasurable (hO.aemeasurable 0)).1 hint)
  rw [IsConsistent, ← integral_map (hO.aemeasurable 0) hf.aestronglyMeasurable] at h
  simpa only [fitCross_sample] using h

/-- **The sample design is invertible with probability tending to one** when the population
design second moment is positive definite and the design has finite second moments: the
determinant of `Ĝ_n` converges in probability to `det G > 0`. -/
theorem withProbTendingToOne_det_fitGram_ne_zero (hO : IsIIDSample O P) {d : 𝒪 → κ → ℝ}
    (hd : ∀ j, Measurable fun o => d o j) (hd2 : ∀ j, MemLp (fun o => d o j) 2 (P.map (O 0)))
    (hG : (Matrix.of fun j k => ∫ o, d o j * d o k ∂(P.map (O 0))).PosDef) :
    WithProbTendingToOne P (fun n => {ω | (fitGram d (fun i : Fin n => O i ω)).det ≠ 0}) := by
  have hc : Continuous fun G : κ → κ → ℝ => (Matrix.of G).det :=
    (continuous_id (X := Matrix κ κ ℝ)).matrix_det
  have hdet := (tendstoInMeasure_fitGram hO hd hd2).comp_continuousAt hc.continuousAt
  refine (hdet.withProbTendingToOne_dist_lt hG.det_pos).mono fun n ω hω h0 => ?_
  simp only [Set.mem_ofPred_eq] at hω
  have e : (Matrix.of fun j k => fitGram d (fun i : Fin n => O i ω) j k) =
      fitGram d (fun i : Fin n => O i ω) := rfl
  rw [e, h0, dist_comm, Real.dist_eq, sub_zero, abs_of_pos hG.det_pos] at hω
  exact lt_irrefl _ hω

/-- **Consistency of least squares for the projection coefficient.** For an i.i.d. sample whose
design coordinates and response have finite second moments, with a positive definite population
design second moment `G = E[d dᵀ]`, the least squares fit converges in probability to
`G⁻¹ E[d r]`. No model is assumed; matrix inversion is continuous at the invertible `G`. -/
theorem tendstoInMeasure_leastSquaresFit (hO : IsIIDSample O P) {d : 𝒪 → κ → ℝ} {r : 𝒪 → ℝ}
    (hd : ∀ j, Measurable fun o => d o j) (hr : Measurable r)
    (hd2 : ∀ j, MemLp (fun o => d o j) 2 (P.map (O 0))) (hr2 : MemLp r 2 (P.map (O 0)))
    (hG : (Matrix.of fun j k => ∫ o, d o j * d o k ∂(P.map (O 0))).PosDef) :
    TendstoInMeasure P (leastSquaresFit d r O) atTop
      (fun _ => (Matrix.of fun j k => ∫ o, d o j * d o k ∂(P.map (O 0)))⁻¹ *ᵥ
        fun j => ∫ o, d o j * r o ∂(P.map (O 0))) := by
  set G : Matrix κ κ ℝ := Matrix.of fun j k => ∫ o, d o j * d o k ∂(P.map (O 0))
  have hdet : G.det ≠ 0 := hG.det_pos.ne'
  have hinv : ContinuousAt (Inv.inv : Matrix κ κ ℝ → Matrix κ κ ℝ) G :=
    continuousAt_matrix_inv G (by rw [Ring.inverse_eq_inv']; exact continuousAt_inv₀ hdet)
  set p₀ : (κ → κ → ℝ) × (κ → ℝ) :=
    ((fun j k => ∫ o, d o j * d o k ∂(P.map (O 0))), fun j => ∫ o, d o j * r o ∂(P.map (O 0)))
  have hi : ContinuousAt (fun p : (κ → κ → ℝ) × (κ → ℝ) => ((Matrix.of p.1)⁻¹, p.2)) p₀ :=
    (ContinuousAt.comp (x := p₀) (g := Inv.inv)
      (f := fun p : (κ → κ → ℝ) × (κ → ℝ) => Matrix.of p.1) hinv
      continuous_fst.continuousAt).prodMk continuous_snd.continuousAt
  have hg : ContinuousAt (fun p : (κ → κ → ℝ) × (κ → ℝ) => (Matrix.of p.1)⁻¹ *ᵥ p.2) p₀ :=
    (continuous_fst.matrix_mulVec continuous_snd).continuousAt.comp
      (g := fun q : Matrix κ κ ℝ × (κ → ℝ) => q.1 *ᵥ q.2) hi
  exact ((tendstoInMeasure_fitGram hO hd hd2).prodMk
    (tendstoInMeasure_fitCross hO hd hr hd2 hr2)).comp_continuousAt hg

end Sample

/-! ### Positive definiteness of the design second moment -/

section PosDef

variable {κ 𝒪 : Type*} [Fintype κ] [MeasurableSpace 𝒪] {ν : Measure 𝒪}

/-- The quadratic form of the design second moment is the second moment of the linear form:
`vᵀ E[d dᵀ] v = E[(d ⬝ v)²]`, for design coordinates with integrable products. -/
theorem dotProduct_gram_mulVec {d : 𝒪 → κ → ℝ}
    (hdd : ∀ j k, Integrable (fun o => d o j * d o k) ν) (v : κ → ℝ) :
    star v ⬝ᵥ ((Matrix.of fun j k => ∫ o, d o j * d o k ∂ν) *ᵥ v) = ∫ o, (d o ⬝ᵥ v) ^ 2 ∂ν := by
  have hint : ∀ j k, Integrable (fun o => v j * (d o j * d o k) * v k) ν := fun j k =>
    ((hdd j k).const_mul (v j)).mul_const (v k)
  have hsq : ∀ o, (d o ⬝ᵥ v) ^ 2 = ∑ j, ∑ k, v j * (d o j * d o k) * v k := fun o => by
    rw [sq, dotProduct, Finset.sum_mul_sum]
    exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => by ring
  simp_rw [hsq]
  rw [integral_finsetSum _ fun j _ => integrable_finsetSum _ fun k _ => hint j k]
  simp only [star_trivial, dotProduct, mulVec, Matrix.of_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [integral_finsetSum _ fun k _ => hint j k]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [integral_mul_const, integral_const_mul]
  ring

/-- **A nondegenerate design has a positive definite second moment.** If the design coordinates
have finite second moments and no nonzero coefficient vector `v` has `d ⬝ v = 0` almost surely,
then `E[d dᵀ]` is positive definite. -/
theorem posDef_gram_of_ae {d : 𝒪 → κ → ℝ} (hd2 : ∀ j, MemLp (fun o => d o j) 2 ν)
    (h : ∀ v : κ → ℝ, (∀ᵐ o ∂ν, d o ⬝ᵥ v = 0) → v = 0) :
    (Matrix.of fun j k => ∫ o, d o j * d o k ∂ν).PosDef := by
  have hdd : ∀ j k, Integrable (fun o => d o j * d o k) ν := fun j k =>
    (hd2 j).integrable_mul (hd2 k)
  refine PosDef.of_dotProduct_mulVec_pos ?_ fun v hv => ?_
  · refine IsHermitian.ext fun j k => ?_
    simp only [star_trivial, Matrix.of_apply]
    exact integral_congr_ae (Eventually.of_forall fun o => mul_comm _ _)
  · rw [dotProduct_gram_mulVec hdd]
    have hsq : ∀ o, (d o ⬝ᵥ v) ^ 2 = ∑ j, ∑ k, v j * (d o j * d o k) * v k := fun o => by
      rw [sq, dotProduct, Finset.sum_mul_sum]
      exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => by ring
    have hi : Integrable (fun o => (d o ⬝ᵥ v) ^ 2) ν := by
      simp_rw [hsq]
      exact integrable_finsetSum _ fun j _ => integrable_finsetSum _ fun k _ =>
        ((hdd j k).const_mul (v j)).mul_const (v k)
    refine lt_of_le_of_ne (integral_nonneg fun o => sq_nonneg _) fun h0 => hv (h v ?_)
    filter_upwards [(integral_eq_zero_iff_of_nonneg (fun o => sq_nonneg _) hi).1 h0.symm]
      with o ho
    exact pow_eq_zero_iff two_ne_zero |>.1 ho

end PosDef

/-! ### The linear outcome regression of a trial -/

section Regression

variable {κ : Type*} [Fintype κ] [DecidableEq κ]

omit [DecidableEq κ] in
/-- **The normal equations at the true coefficient.** If `w(C)` is a design measurable in the
conditioning variable `C`, and the conditional mean of `Y` given `C` is `w(C) ⬝ ξ₀`, then
`E[w wᵀ] ξ₀ = E[w Y]`: the tower property, with each coordinate of `w(C)` taken out of the
conditional expectation. -/
theorem gram_mulVec_eq_cross_of_condExp {Ω 𝒞 : Type*} [MeasurableSpace Ω] [MeasurableSpace 𝒞]
    {μ : Measure Ω} [IsFiniteMeasure μ] {C : Ω → 𝒞} (hC : Measurable C) {w : 𝒞 → κ → ℝ}
    (hw : ∀ j, Measurable fun c => w c j) {Y : Ω → ℝ} (hY : Integrable Y μ)
    (hww : ∀ j k, Integrable (fun ω => w (C ω) j * w (C ω) k) μ)
    (hwY : ∀ j, Integrable (fun ω => w (C ω) j * Y ω) μ) {ξ₀ : κ → ℝ}
    (hreg : μ[Y | MeasurableSpace.comap C inferInstance] =ᵐ[μ] fun ω => w (C ω) ⬝ᵥ ξ₀) :
    (Matrix.of fun j k => ∫ ω, w (C ω) j * w (C ω) k ∂μ) *ᵥ ξ₀ =
      fun j => ∫ ω, w (C ω) j * Y ω ∂μ := by
  funext j
  have hm := hC.comap_le
  have hz : StronglyMeasurable[MeasurableSpace.comap C inferInstance] fun ω => w (C ω) j :=
    ((hw j).comp (comap_measurable C)).stronglyMeasurable
  have h1 := condExp_mul_of_stronglyMeasurable_left hz (hwY j) hY
  rw [← integral_condExp hm (f := fun ω => w (C ω) j * Y ω)]
  change _ = ∫ ω, μ[(fun ω => w (C ω) j) * Y | MeasurableSpace.comap C inferInstance] ω ∂μ
  rw [integral_congr_ae (h1.trans (Filter.EventuallyEq.mul (ae_eq_refl _) hreg))]
  simp only [Pi.mul_apply, dotProduct, Finset.mul_sum, Matrix.mulVec]
  rw [integral_finsetSum _ fun k _ => ?_]
  · refine Finset.sum_congr rfl fun k _ => ?_
    rw [Matrix.of_apply, ← integral_mul_const]
    exact integral_congr_ae (Eventually.of_forall fun ω => by simp only; ring)
  · exact ((hww j k).mul_const (ξ₀ k)).congr (Eventually.of_forall fun ω => by simp only; ring)

variable {Ω Ξ 𝒲 : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ] [MeasurableSpace 𝒲]
  {μ : Measure Ω} {P : Measure Ξ} {W : Ω → 𝒲} {A : Ω → Bool} {Yo : Ω → ℝ}

/-- The design row `z(a, w)` of a trial record `(w, a, y)`. -/
def recordDesign (z : Bool → 𝒲 → κ → ℝ) (o : 𝒲 × Bool × ℝ) : κ → ℝ := z o.2.1 o.1

/-- The response `y` of a trial record `(w, a, y)`. -/
def recordResponse (o : 𝒲 × Bool × ℝ) : ℝ := o.2.2

omit [Fintype κ] [DecidableEq κ] in
/-- The coordinates of the record design are measurable when those of each arm design are. -/
theorem measurable_recordDesign {z : Bool → 𝒲 → κ → ℝ} (hz : ∀ a j, Measurable fun w => z a w j)
    (j : κ) : Measurable fun o : 𝒲 × Bool × ℝ => recordDesign z o j := by
  have h : Measurable fun q : 𝒲 × Bool => z q.2 q.1 j :=
    measurable_from_prod_countable_left fun a => hz a j
  exact h.comp (measurable_fst.prodMk (measurable_fst.comp measurable_snd))

/-- **Consistency of least squares for a linear outcome regression.** Let the trial variables
`W` (covariates), `A` (arm) and `Yo` (observed outcome) be measurable, the design coordinates
`z(A, W)_j` and the outcome have finite second moments, the population design second moment
`E[z zᵀ]` be positive definite, and the regression of the outcome on the covariates and the arm
be linear, `E[Yo | W, A] = z(A, W)ᵀξ₀` (`PointTreatment.IsOutcomeRegression`). Then for an
i.i.d. sample of records with the law of `(W, A, Yo)` the least squares fit converges in
probability to `ξ₀`. No randomization is needed for this step; it enters when `z(t, ·)ᵀξ₀` is
read as the conditional mean of a potential outcome. -/
theorem tendstoInMeasure_leastSquaresFit_of_isOutcomeRegression [IsProbabilityMeasure μ]
    [IsProbabilityMeasure P] (hW : Measurable W) (hA : Measurable A) (hYo : Measurable Yo)
    {z : Bool → 𝒲 → κ → ℝ} (hz : ∀ a j, Measurable fun w => z a w j)
    (hz2 : ∀ j, MemLp (fun ω => z (A ω) (W ω) j) 2 μ) (hY2 : MemLp Yo 2 μ) {ξ₀ : κ → ℝ}
    (hreg : IsOutcomeRegression μ A W Yo fun a w => z a w ⬝ᵥ ξ₀)
    (hG : (Matrix.of fun j k => ∫ ω, z (A ω) (W ω) j * z (A ω) (W ω) k ∂μ).PosDef)
    {O : ℕ → Ξ → 𝒲 × Bool × ℝ} (hO : IsIIDSample O P)
    (hlaw : P.map (O 0) = μ.map fun ω => (W ω, A ω, Yo ω)) :
    TendstoInMeasure P (leastSquaresFit (recordDesign z) recordResponse O) atTop
      (fun _ => ξ₀) := by
  have hD : Measurable fun ω => (W ω, A ω, Yo ω) := hW.prodMk (hA.prodMk hYo)
  have hdm := measurable_recordDesign hz
  have hrm : Measurable (recordResponse (𝒲 := 𝒲)) := measurable_snd.comp measurable_snd
  have hd2 : ∀ j, MemLp (fun o => recordDesign z o j) 2 (P.map (O 0)) := fun j => by
    rw [hlaw, memLp_map_measure_iff (hdm j).aestronglyMeasurable hD.aemeasurable]
    exact hz2 j
  have hr2 : MemLp recordResponse 2 (P.map (O 0)) := by
    rw [hlaw, memLp_map_measure_iff hrm.aestronglyMeasurable hD.aemeasurable]
    exact hY2
  have hGμ : ∀ j k, ∫ o, recordDesign z o j * recordDesign z o k ∂(P.map (O 0)) =
      ∫ ω, z (A ω) (W ω) j * z (A ω) (W ω) k ∂μ := fun j k => by
    rw [hlaw, integral_map (f := fun o => recordDesign z o j * recordDesign z o k)
      hD.aemeasurable ((hdm j).mul (hdm k)).aestronglyMeasurable]
    rfl
  have hcμ : ∀ j, ∫ o, recordDesign z o j * recordResponse o ∂(P.map (O 0)) =
      ∫ ω, z (A ω) (W ω) j * Yo ω ∂μ := fun j => by
    rw [hlaw, integral_map (f := fun o => recordDesign z o j * recordResponse o)
      hD.aemeasurable ((hdm j).mul hrm).aestronglyMeasurable]
    rfl
  have hG' : (Matrix.of fun j k => ∫ o, recordDesign z o j * recordDesign z o k
      ∂(P.map (O 0))).PosDef := by
    simp only [hGμ]; exact hG
  have h := tendstoInMeasure_leastSquaresFit hO hdm hrm hd2 hr2 hG'
  simp only [hGμ, hcμ] at h
  have hw : ∀ j, Measurable fun q : 𝒲 × Bool => z q.2 q.1 j := fun j =>
    measurable_from_prod_countable_left fun a => hz a j
  have hnorm := gram_mulVec_eq_cross_of_condExp (C := fun ω => (W ω, A ω)) (hW.prodMk hA)
    (w := fun q => z q.2 q.1) hw (hY2.integrable one_le_two)
    (fun j k => (hz2 j).integrable_mul (hz2 k)) (fun j => (hz2 j).integrable_mul hY2) hreg.2
  rw [← hnorm, mulVec_mulVec, nonsing_inv_mul _ (isUnit_iff_ne_zero.2 hG.det_pos.ne'),
    one_mulVec] at h
  exact h

end Regression

end PopulationAdjustment

end CausalInference
