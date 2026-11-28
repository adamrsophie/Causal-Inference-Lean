/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.Estimation.VectorZEstimator
public import CausalInference.Estimation.Sandwich

/-!
# The matrix sandwich variance estimator

For a Z-estimator `θh` of a parameter in `ℝ^ι` with estimating function `ψ` and Jacobian matrix
`J`, the asymptotic covariance of `√n (θh n - θ₀)` is the sandwich `A⁻¹ B A⁻ᵀ` with bread
`A = breadMatrix (μ.map (O 0)) J θ₀` and meat `B = meatMatrix (μ.map (O 0)) ψ θ₀`
(`vectorZEstimator_tendstoInDistribution`). The plug-in estimators replace expectations by sample
means and `θ₀` by `θh n`.

## Main definitions

* `CausalInference.breadMatrixHat`, `CausalInference.meatMatrixHat`: the empirical bread
  `-n⁻¹ ∑_{i < n} J (O i) (θh n)` and meat `n⁻¹ ∑_{i < n} ψ (O i) (θh n) ψ (O i) (θh n)ᵀ`.
* `CausalInference.sandwichMatrixHat`: the sandwich covariance estimate
  `n⁻¹ Âₙ⁻¹ B̂ₙ Âₙ⁻ᵀ` of the covariance of `θh n`.

At a finite sample size the empirical bread may be singular; there `Âₙ⁻¹ = 0` by the convention
of `Matrix.inv`. This affects no result below: the empirical bread converges to a nonsingular
bread, and matrix inversion is continuous there, so the convention matters only on events of
probability tending to zero.

## Main results

* `CausalInference.continuousAt_sandwich`: `(A, B) ↦ A⁻¹ B A⁻ᵀ` is continuous at a pair with `A`
  nonsingular.
* `CausalInference.breadMatrixHat_tendstoInMeasure` and
  `CausalInference.meatMatrixHat_tendstoInMeasure`: the empirical bread and meat are
  consistent entrywise, through the uniform law of large numbers.
* `CausalInference.sandwichMatrixHat_tendstoInMeasure`: **consistency of the sandwich
  estimator**: every entry of `n` times the sandwich estimate converges in probability to the
  corresponding entry of `A⁻¹ B A⁻ᵀ`.
* `CausalInference.breadMatrix_unique`, `CausalInference.meatMatrix_unique`,
  `CausalInference.sandwich_unique`: for a one dimensional parameter the bread, the meat and the
  sandwich are `sandwichBread`, `sandwichMeat` and `B / A²` of
  `CausalInference.Estimation.Sandwich`.

References: P. J. Huber (1967), *The behavior of maximum likelihood estimates under nonstandard
conditions*; H. White (1980), *A heteroskedasticity-consistent covariance matrix estimator and a
direct test for heteroskedasticity*, Econometrica; L. A. Stefanski and D. D. Boos (2002),
*The calculus of M-estimation*, The American Statistician.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Finset Matrix
open scoped Topology ENNReal NNReal RealInnerProductSpace

namespace CausalInference

variable {Ω 𝒪 : Type*} {mΩ : MeasurableSpace Ω} [MeasurableSpace 𝒪] {μ : Measure Ω}
  {O : ℕ → Ω → 𝒪} {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The empirical bread `-n⁻¹ ∑_{i < n} J (O i) (θh n)`. -/
noncomputable def breadMatrixHat (O : ℕ → Ω → 𝒪) (J : 𝒪 → EuclideanSpace ℝ ι → Matrix ι ι ℝ)
    (θh : ℕ → Ω → EuclideanSpace ℝ ι) (n : ℕ) (ω : Ω) : Matrix ι ι ℝ :=
  Matrix.of fun i j ↦ -sampleMean (fun z ↦ J z (θh n ω) i j) O n ω

/-- The empirical meat `n⁻¹ ∑_{i < n} ψ (O i) (θh n) ψ (O i) (θh n)ᵀ`. -/
noncomputable def meatMatrixHat (O : ℕ → Ω → 𝒪)
    (ψ : 𝒪 → EuclideanSpace ℝ ι → EuclideanSpace ℝ ι) (θh : ℕ → Ω → EuclideanSpace ℝ ι) (n : ℕ)
    (ω : Ω) : Matrix ι ι ℝ :=
  Matrix.of fun i j ↦ sampleMean (fun z ↦ ψ z (θh n ω) i * ψ z (θh n ω) j) O n ω

/-- The sandwich covariance estimate `n⁻¹ Âₙ⁻¹ B̂ₙ Âₙ⁻ᵀ` of the covariance of `θh n`. Where the
empirical bread is singular its inverse is `0`. -/
noncomputable def sandwichMatrixHat (O : ℕ → Ω → 𝒪)
    (ψ : 𝒪 → EuclideanSpace ℝ ι → EuclideanSpace ℝ ι)
    (J : 𝒪 → EuclideanSpace ℝ ι → Matrix ι ι ℝ) (θh : ℕ → Ω → EuclideanSpace ℝ ι) (n : ℕ)
    (ω : Ω) : Matrix ι ι ℝ :=
  (n : ℝ)⁻¹ • ((breadMatrixHat O J θh n ω)⁻¹ * meatMatrixHat O ψ θh n ω *
    ((breadMatrixHat O J θh n ω)⁻¹)ᵀ)

/-- **Continuity of the sandwich.** The map `(A, B) ↦ A⁻¹ B A⁻ᵀ`, on pairs of arrays
`ι → ι → ℝ` with the sup norm, is continuous at a pair with `A` nonsingular: matrix inversion is
continuous where the determinant does not vanish. -/
theorem continuousAt_sandwich {A B : Matrix ι ι ℝ} (hA : A.det ≠ 0) :
    ContinuousAt (fun p : (ι → ι → ℝ) × (ι → ι → ℝ) ↦
      (Matrix.of.symm ((Matrix.of p.1)⁻¹ * Matrix.of p.2 * ((Matrix.of p.1)⁻¹)ᵀ) :
        ι → ι → ℝ)) (Matrix.of.symm A, Matrix.of.symm B) := by
  have hdet : ContinuousAt Ring.inverse A.det := by
    have := NormedRing.inverse_continuousAt (Units.mk0 A.det hA)
    rwa [Units.val_mk0] at this
  have hinv : ContinuousAt (Inv.inv : Matrix ι ι ℝ → Matrix ι ι ℝ) A :=
    continuousAt_matrix_inv A hdet
  have hc : Continuous (fun q : Matrix ι ι ℝ × Matrix ι ι ℝ ↦ q.1 * q.2 * q.1ᵀ) :=
    (continuous_fst.matrix_mul continuous_snd).matrix_mul continuous_fst.matrix_transpose
  have hof : Continuous (fun p : (ι → ι → ℝ) × (ι → ι → ℝ) ↦ (Matrix.of p.1, Matrix.of p.2)) :=
    continuous_id
  have hg : ContinuousAt (fun q : Matrix ι ι ℝ × Matrix ι ι ℝ ↦ (q.1⁻¹, q.2)) (A, B) :=
    (hinv.comp continuousAt_fst).prodMk continuousAt_snd
  have hsymm : Continuous (Matrix.of.symm : Matrix ι ι ℝ → ι → ι → ℝ) := continuous_id
  have h1 := ContinuousAt.comp_of_eq (hc.continuousAt.comp hg)
    (hof.continuousAt (x := (Matrix.of.symm A, Matrix.of.symm B))) rfl
  exact hsymm.continuousAt.comp h1

omit [DecidableEq ι] in
/-- **Consistency of the empirical bread.** If every entry `z ↦ J z θ i j` is measurable on a
closed ball `K` around `θ₀`, continuous on `K` for almost every observation value and dominated
there by an integrable envelope, and `θh` is consistent for `θ₀`, then every entry of the
empirical bread converges in probability to the corresponding entry of the bread. -/
theorem breadMatrixHat_tendstoInMeasure [IsProbabilityMeasure μ] (hO : IsIIDSample O μ)
    {J : 𝒪 → EuclideanSpace ℝ ι → Matrix ι ι ℝ} {θ₀ : EuclideanSpace ℝ ι} {r : ℝ} (hr : 0 < r)
    (hJm : ∀ θ ∈ Metric.closedBall θ₀ r, ∀ i j, Measurable fun z ↦ J z θ i j)
    (hcont : ∀ᵐ z ∂(μ.map (O 0)), ∀ i j,
      ContinuousOn (fun θ ↦ J z θ i j) (Metric.closedBall θ₀ r))
    {H : 𝒪 → ℝ} (hH : Integrable H (μ.map (O 0)))
    (hdom : ∀ᵐ z ∂(μ.map (O 0)), ∀ θ ∈ Metric.closedBall θ₀ r, ∀ i j, |J z θ i j| ≤ H z)
    {θh : ℕ → Ω → EuclideanSpace ℝ ι} (hθ : TendstoInMeasure μ θh atTop (fun _ ↦ θ₀))
    (i j : ι) :
    TendstoInMeasure μ (fun n ω ↦ breadMatrixHat O J θh n ω i j) atTop
      (fun _ ↦ breadMatrix (μ.map (O 0)) J θ₀ i j) := by
  have hK := Metric.closedBall_mem_nhds θ₀ hr
  obtain ⟨hMc, hunif⟩ := uniform_law_of_large_numbers_real hO (isCompact_closedBall θ₀ r)
    (ψ := fun z θ ↦ J z θ i j) (fun θ hθ ↦ hJm θ hθ i j) (hcont.mono fun z hz ↦ hz i j) hH
    (hdom.mono fun z hz θ hθ ↦ hz θ hθ i j)
  exact (hunif.comp_tendstoInMeasure hK (hMc.continuousAt hK) hθ).comp_continuousAt
    (g := fun x : ℝ ↦ -x) continuous_neg.continuousAt

omit [DecidableEq ι] in
/-- A product of two coordinates is bounded by the squared norm. -/
lemma abs_apply_mul_apply_le (x : EuclideanSpace ℝ ι) (i j : ι) : |x i * x j| ≤ ‖x‖ ^ 2 := by
  rw [abs_mul, sq]
  have hi : |x i| ≤ ‖x‖ := by simpa [Real.norm_eq_abs] using PiLp.norm_apply_le x i
  have hj : |x j| ≤ ‖x‖ := by simpa [Real.norm_eq_abs] using PiLp.norm_apply_le x j
  exact mul_le_mul hi hj (abs_nonneg _) (norm_nonneg _)

omit [DecidableEq ι] in
/-- **Consistency of the empirical meat.** If `ψ z` is continuous on a closed ball `K` around
`θ₀` for almost every observation value, `z ↦ ψ z θ` is measurable for `θ ∈ K`,
`‖ψ z θ‖² ≤ G z` on `K` for an integrable envelope `G`, and `θh` is consistent for `θ₀`, then
every entry of the empirical meat converges in probability to the corresponding entry of the
meat. -/
theorem meatMatrixHat_tendstoInMeasure [IsProbabilityMeasure μ] (hO : IsIIDSample O μ)
    {ψ : 𝒪 → EuclideanSpace ℝ ι → EuclideanSpace ℝ ι} {θ₀ : EuclideanSpace ℝ ι} {r : ℝ}
    (hr : 0 < r) (hψm : ∀ θ ∈ Metric.closedBall θ₀ r, Measurable fun z ↦ ψ z θ)
    (hcontψ : ∀ᵐ z ∂(μ.map (O 0)), ContinuousOn (ψ z) (Metric.closedBall θ₀ r))
    {G : 𝒪 → ℝ} (hG : Integrable G (μ.map (O 0)))
    (hdomG : ∀ᵐ z ∂(μ.map (O 0)), ∀ θ ∈ Metric.closedBall θ₀ r, ‖ψ z θ‖ ^ 2 ≤ G z)
    {θh : ℕ → Ω → EuclideanSpace ℝ ι} (hθ : TendstoInMeasure μ θh atTop (fun _ ↦ θ₀))
    (i j : ι) :
    TendstoInMeasure μ (fun n ω ↦ meatMatrixHat O ψ θh n ω i j) atTop
      (fun _ ↦ meatMatrix (μ.map (O 0)) ψ θ₀ i j) := by
  have hK := Metric.closedBall_mem_nhds θ₀ hr
  have hp : ∀ k, Continuous fun x : EuclideanSpace ℝ ι ↦ x k := fun k ↦
    (EuclideanSpace.proj (𝕜 := ℝ) k).continuous
  obtain ⟨hNc, hunif⟩ := uniform_law_of_large_numbers_real hO (isCompact_closedBall θ₀ r)
    (ψ := fun z θ ↦ ψ z θ i * ψ z θ j)
    (fun θ hθ ↦ ((hp i).measurable.comp (hψm θ hθ)).mul ((hp j).measurable.comp (hψm θ hθ)))
    (hcontψ.mono fun z hz ↦ ((hp i).comp_continuousOn hz).mul ((hp j).comp_continuousOn hz)) hG
    (hdomG.mono fun z hz θ hθ ↦ (abs_apply_mul_apply_le _ i j).trans (hz θ hθ))
  exact hunif.comp_tendstoInMeasure hK (hNc.continuousAt hK) hθ

/-- **Consistency of the sandwich covariance estimator.** Under the hypotheses of
`breadMatrixHat_tendstoInMeasure` and `meatMatrixHat_tendstoInMeasure` and a nonsingular bread
`A`, every entry of `n` times the sandwich estimate converges in probability to the
corresponding entry of `A⁻¹ B A⁻ᵀ`, the asymptotic covariance of `√n (θh n - θ₀)`. -/
theorem sandwichMatrixHat_tendstoInMeasure [IsProbabilityMeasure μ] (hO : IsIIDSample O μ)
    {ψ : 𝒪 → EuclideanSpace ℝ ι → EuclideanSpace ℝ ι}
    {J : 𝒪 → EuclideanSpace ℝ ι → Matrix ι ι ℝ} {θ₀ : EuclideanSpace ℝ ι} {r : ℝ} (hr : 0 < r)
    (hψm : ∀ θ ∈ Metric.closedBall θ₀ r, Measurable fun z ↦ ψ z θ)
    (hJm : ∀ θ ∈ Metric.closedBall θ₀ r, ∀ i j, Measurable fun z ↦ J z θ i j)
    (hderiv : ∀ᵐ z ∂(μ.map (O 0)), ∀ θ ∈ Metric.closedBall θ₀ r,
      HasFDerivAt (ψ z) (Matrix.toEuclideanCLM (𝕜 := ℝ) (J z θ)) θ)
    (hcont : ∀ᵐ z ∂(μ.map (O 0)), ∀ i j,
      ContinuousOn (fun θ ↦ J z θ i j) (Metric.closedBall θ₀ r))
    {H : 𝒪 → ℝ} (hH : Integrable H (μ.map (O 0)))
    (hdom : ∀ᵐ z ∂(μ.map (O 0)), ∀ θ ∈ Metric.closedBall θ₀ r, ∀ i j, |J z θ i j| ≤ H z)
    {G : 𝒪 → ℝ} (hG : Integrable G (μ.map (O 0)))
    (hdomG : ∀ᵐ z ∂(μ.map (O 0)), ∀ θ ∈ Metric.closedBall θ₀ r, ‖ψ z θ‖ ^ 2 ≤ G z)
    (hA : (breadMatrix (μ.map (O 0)) J θ₀).det ≠ 0) {θh : ℕ → Ω → EuclideanSpace ℝ ι}
    (hθ : TendstoInMeasure μ θh atTop (fun _ ↦ θ₀)) (i j : ι) :
    TendstoInMeasure μ (fun (n : ℕ) ω ↦ ((n : ℝ) • sandwichMatrixHat O ψ J θh n ω) i j) atTop
      (fun _ ↦ ((breadMatrix (μ.map (O 0)) J θ₀)⁻¹ * meatMatrix (μ.map (O 0)) ψ θ₀ *
        ((breadMatrix (μ.map (O 0)) J θ₀)⁻¹)ᵀ) i j) := by
  set A := breadMatrix (μ.map (O 0)) J θ₀
  set B := meatMatrix (μ.map (O 0)) ψ θ₀
  have h1 := breadMatrixHat_tendstoInMeasure hO hr hJm hcont hH hdom hθ
  have h2 := meatMatrixHat_tendstoInMeasure hO hr hψm
    (hderiv.mono fun z hz θ hθ ↦ (hz θ hθ).continuousAt.continuousWithinAt) hG hdomG hθ
  have h1' : TendstoInMeasure μ (fun n ω ↦ (fun k l ↦ breadMatrixHat O J θh n ω k l :
      ι → ι → ℝ)) atTop (fun _ ↦ Matrix.of.symm A) :=
    tendstoInMeasure_pi (X := fun k n ω l ↦ breadMatrixHat O J θh n ω k l) fun k ↦
      tendstoInMeasure_pi (X := fun l n ω ↦ breadMatrixHat O J θh n ω k l) fun l ↦ h1 k l
  have h2' : TendstoInMeasure μ (fun n ω ↦ (fun k l ↦ meatMatrixHat O ψ θh n ω k l :
      ι → ι → ℝ)) atTop (fun _ ↦ Matrix.of.symm B) :=
    tendstoInMeasure_pi (X := fun k n ω l ↦ meatMatrixHat O ψ θh n ω k l) fun k ↦
      tendstoInMeasure_pi (X := fun l n ω ↦ meatMatrixHat O ψ θh n ω k l) fun l ↦ h2 k l
  have h3 := ((TendstoInMeasure.prodMk h1' h2').comp_continuousAt
    (continuousAt_sandwich hA)).comp_continuousAt
    (g := fun F : ι → ι → ℝ ↦ F i j) (continuous_apply_apply i j).continuousAt
  refine h3.congr_withProbTendingToOne (A := fun n ↦ {ω | (n : ℝ) ≠ 0}) ?_ fun n ω hω ↦ ?_
  · refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with n hn
    have : {ω : Ω | (n : ℝ) ≠ 0}ᶜ = ∅ := by
      ext ω; simp [Nat.pos_iff_ne_zero.1 hn]
    rw [this, measure_empty]
  · simp only [Set.mem_ofPred_eq] at hω
    simp only [sandwichMatrixHat, smul_smul, mul_inv_cancel₀ hω, one_smul]
    rfl

/-! ### The one dimensional parameter -/

/-- For a one dimensional parameter, the bread of `J z θ = ψ' z θ` is the scalar bread. -/
theorem breadMatrix_unique (ν : Measure 𝒪) (ψ' : 𝒪 → ℝ → ℝ) (θ : EuclideanSpace ℝ Unit) :
    breadMatrix ν (fun z θ ↦ Matrix.of fun _ _ ↦ ψ' z (θ ())) θ () () =
      sandwichBread ν ψ' (θ ()) := rfl

/-- For a one dimensional parameter, the meat of `ψ z θ = ψ₁ z θ` is the scalar meat. -/
theorem meatMatrix_unique (ν : Measure 𝒪) (ψ₁ : 𝒪 → ℝ → ℝ) (θ : EuclideanSpace ℝ Unit) :
    meatMatrix ν (fun z θ ↦ WithLp.toLp 2 (fun _ ↦ ψ₁ z (θ ()))) θ () () =
      sandwichMeat ν ψ₁ (θ ()) := by
  simp [meatMatrix, sandwichMeat, sq]

/-- For `1 × 1` matrices with `A = a ≠ 0` and `B = b`, the sandwich `A⁻¹ B A⁻ᵀ` is `b / a²`. -/
theorem sandwich_unique {A B : Matrix Unit Unit ℝ} (hA : A () () ≠ 0) :
    (A⁻¹ * B * A⁻¹ᵀ) () () = B () () / A () () ^ 2 := by
  have hinv : A⁻¹ = Matrix.of fun _ _ ↦ (A () ())⁻¹ := by
    refine Matrix.inv_eq_left_inv ?_
    ext u v
    simp [Matrix.mul_apply, inv_mul_cancel₀ hA]
  rw [hinv]
  simp [Matrix.mul_apply]
  field_simp

end CausalInference
