/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.PopulationAdjustment.WeightedNormalityLimit

/-!
# The sandwich variance estimator of the weighted arm mean

The weighted (matching adjusted) arm mean `m̂ₙ` is the last coordinate of the root
`θ̂ₙ = (β̂ₙ, m̂ₙ)` of the stacked estimating equations of `WeightedNormalityEquations`, and
`√n (m̂ₙ - m₀) → N(0, σ²)` with the sandwich variance `σ² = weightedArmVariance = E[IF²]`
(`sampleBalancedArmMean_tendstoInDistribution`). The plug-in sandwich estimate
`sandwichMatrixHat` of the covariance of `θ̂ₙ` has the last diagonal entry `σ̂ₙ² / n`. This file
proves:

* **consistency**: `n` times the last diagonal entry of the sandwich estimate converges in
  probability to `σ²` (`sandwichMatrixHat_weighted_tendstoInMeasure`), under the conditions of
  the normal limit: an i.i.d. sample, measurable bounded features, the margin condition,
  `P(A = a) > 0` and a square integrable outcome. No fourth moment is needed: the meat is the mean
  of products of two coordinates of the estimating function, each bounded on a ball by a constant
  times `1 + |Y|`, so `E[Y²] < ∞` gives the integrable envelope;
* the entry is a mean of squares, hence nonnegative for every sample
  (`sandwichMatrixHat_weighted_nonneg`), so its square root is a genuine scale estimate;
* **the explicit form**: when the empirical tilted second moment matrix `M̂` is nonsingular and
  the empirical tilted mass `q̂` of the arm is not zero, the estimate is the empirical mean of the
  squared estimated influence values
  `ÎF(z) = (1{s = a} ŵ(x) (y - m̂) - ĉᵀ M̂⁻¹ ŵ(x) (φ(x) - t)) / q̂`, with the estimated tilt
  `ŵ = w_{β̂ₙ}`, the empirical coupling vector `ĉ = n⁻¹ ∑ᵢ 1{Aᵢ = a} ŵ(Xᵢ) (Yᵢ - m̂) (φ(Xᵢ) - t)`
  and `q̂ = n⁻¹ ∑ᵢ 1{Aᵢ = a} ŵ(Xᵢ)` (`sandwichMatrixHat_weighted_eq_sampleWeightedArmVariance`).
  The explicit form is consistent as well (`sampleWeightedArmVariance_tendstoInMeasure`): the
  nondegeneracy holds with probability tending to one.

The cross covariance estimate `weightedInfluenceCovHat` of two arms (the mean of the products of
the estimated influence values of the two arms) is defined here; its diagonal is the sandwich
entry (`weightedInfluenceCovHat_self`).

## Main definitions

* `sampleTiltedSecondMoment`, `sampleWeightedCoupling`, `sampleWeightedArmMass`: `M̂`, `ĉ`, `q̂`.
* `sampleWeightedArmInfluence`, `sampleWeightedArmVariance`: `ÎF` and `n⁻¹ ∑ᵢ ÎF(Zᵢ)²`.
* `weightedInfluenceCovHat`: the cross covariance estimate of the influence values of two arms.

## Main results

* `inv_fromBlocks_mulVec_inr`: the last coordinate of the inverse of a block lower triangular
  bread applied to a vector.
* `mul_of_integral_mul_transpose_apply`, `mul_of_sampleMean_mul_transpose_apply`: an entry of
  `C B Dᵀ` for a matrix `B` of means of products is the mean of a product.
* `sandwich_weightedEstFun_eq_weightedArmVariance`: the last diagonal entry of `A⁻¹ B A⁻ᵀ` is
  `σ² = E[IF²]`.
* `sandwichMatrixHat_weighted_tendstoInMeasure`, `sandwichMatrixHat_weighted_nonneg`.
* `breadMatrixHat_weightedEstJac`: the empirical bread is block lower triangular.
* `sandwichMatrixHat_weighted_eq_sampleWeightedArmVariance`,
  `sampleWeightedArmVariance_tendstoInMeasure`.

## References

* J. E. Signorovitch and coauthors, PharmacoEconomics 28 (2010).
* L. A. Stefanski and D. D. Boos (2002), *The calculus of M-estimation*, The American
  Statistician.
* P. J. Huber (1967), *The behavior of maximum likelihood estimates under nonstandard
  conditions*.
* H. White (1982), *Maximum likelihood estimation of misspecified models*, Econometrica.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Finset Matrix
open scoped Topology ENNReal

namespace CausalInference

namespace PopulationAdjustment

open PointTreatment

/-! ### Matrix algebra -/

section Algebra

variable {ι : Type*} [Fintype ι]

/-- **An entry of `C B Dᵀ` for a matrix of means of products** under a measure: if
`B k l = ∫ f_k g_l` with integrable products, then `(C B Dᵀ) i j = ∫ (C f)_i (D g)_j`. -/
theorem mul_of_integral_mul_transpose_apply {𝒪 : Type*} [MeasurableSpace 𝒪] {ν : Measure 𝒪}
    (C D : Matrix ι ι ℝ) {f g : 𝒪 → ι → ℝ}
    (hfg : ∀ k l, Integrable (fun z => f z k * g z l) ν) (i j : ι) :
    (C * Matrix.of (fun k l => ∫ z, f z k * g z l ∂ν) * Dᵀ) i j =
      ∫ z, (C *ᵥ f z) i * (D *ᵥ g z) j ∂ν := by
  have hpt : ∀ z, (C *ᵥ f z) i * (D *ᵥ g z) j =
      ∑ k, ∑ l, C i k * D j l * (f z k * g z l) := by
    intro z
    rw [mulVec, mulVec, dotProduct, dotProduct, Finset.sum_mul_sum]
    exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => by ring
  simp_rw [hpt]
  rw [integral_finsetSum _ fun k _ => integrable_finsetSum _ fun l _ => (hfg k l).const_mul _]
  simp only [Matrix.mul_apply, Matrix.of_apply, Matrix.transpose_apply, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [integral_finsetSum _ fun l _ => (hfg k l).const_mul _]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [integral_const_mul]
  ring

omit [Fintype ι] in
/-- The sample mean of a finite sum is the sum of the sample means. -/
theorem sampleMean_fun_sum {Ω 𝒪 : Type*} (s : Finset ι) (F : ι → 𝒪 → ℝ) (O : ℕ → Ω → 𝒪)
    (n : ℕ) (ω : Ω) :
    sampleMean (fun z => ∑ k ∈ s, F k z) O n ω = ∑ k ∈ s, sampleMean (F k) O n ω := by
  simp only [sampleMean]
  rw [Finset.sum_comm, Finset.mul_sum]

/-- The sample mean of a constant multiple is the multiple of the sample mean. -/
theorem sampleMean_fun_const_mul {Ω 𝒪 : Type*} (c : ℝ) (F : 𝒪 → ℝ) (O : ℕ → Ω → 𝒪) (n : ℕ)
    (ω : Ω) : sampleMean (fun z => c * F z) O n ω = c * sampleMean F O n ω := by
  simp only [sampleMean, ← Finset.mul_sum]
  ring

/-- **An entry of `C B Dᵀ` for a matrix of sample means of products**: if
`B k l = n⁻¹ ∑ᵢ f_k(Oᵢ) g_l(Oᵢ)`, then `(C B Dᵀ) i j = n⁻¹ ∑ᵢ (C f(Oᵢ))_i (D g(Oᵢ))_j`. -/
theorem mul_of_sampleMean_mul_transpose_apply {Ω 𝒪 : Type*} (C D : Matrix ι ι ℝ)
    (f g : 𝒪 → ι → ℝ) (O : ℕ → Ω → 𝒪) (n : ℕ) (ω : Ω) (i j : ι) :
    (C * Matrix.of (fun k l => sampleMean (fun z => f z k * g z l) O n ω) * Dᵀ) i j =
      sampleMean (fun z => (C *ᵥ f z) i * (D *ᵥ g z) j) O n ω := by
  have hpt : ∀ z, (C *ᵥ f z) i * (D *ᵥ g z) j =
      ∑ k, ∑ l, C i k * D j l * (f z k * g z l) := by
    intro z
    rw [mulVec, mulVec, dotProduct, dotProduct, Finset.sum_mul_sum]
    exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => by ring
  simp only [hpt, sampleMean_fun_sum, sampleMean_fun_const_mul, Matrix.mul_apply,
    Matrix.of_apply, Matrix.transpose_apply, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
  ring

variable {p : ℕ}

/-- The determinant of a block lower triangular bread `[[-M, 0], [-cᵀ, q]]`. -/
theorem det_fromBlocks_bread (M : Matrix (Fin p) (Fin p) ℝ) (c : Fin p → ℝ) (q : ℝ) :
    (Matrix.fromBlocks (-M) 0 (Matrix.of fun (_ : Unit) k => -c k)
      (Matrix.of fun _ _ => q)).det = (-1) ^ p * M.det * q := by
  rw [Matrix.det_fromBlocks_zero₁₂, Matrix.det_neg, Matrix.det_unique (n := Unit)]
  simp

/-- **The last coordinate of the inverse bread applied to a vector.** For the block lower
triangular matrix `A = [[-M, 0], [-cᵀ, q]]` with `M` nonsingular and `q ≠ 0`,
`(A⁻¹ v)_last = (v_last - cᵀ M⁻¹ v_first) / q`. -/
theorem inv_fromBlocks_mulVec_inr {M : Matrix (Fin p) (Fin p) ℝ} {c : Fin p → ℝ} {q : ℝ}
    (hM : M.det ≠ 0) (hq : q ≠ 0) (v : Fin p ⊕ Unit → ℝ) :
    ((Matrix.fromBlocks (-M) 0 (Matrix.of fun (_ : Unit) k => -c k)
      (Matrix.of fun _ _ => q))⁻¹ *ᵥ v) (Sum.inr ()) =
      (v (Sum.inr ()) - c ⬝ᵥ (M⁻¹ *ᵥ fun j => v (Sum.inl j))) / q := by
  set A := Matrix.fromBlocks (-M) 0 (Matrix.of fun (_ : Unit) k => -c k)
    (Matrix.of fun _ _ => q) with hAdef
  have hA : IsUnit A.det := isUnit_iff_ne_zero.2 (by
    rw [hAdef, det_fromBlocks_bread]
    exact mul_ne_zero (mul_ne_zero (pow_ne_zero _ (by norm_num)) hM) hq)
  have hMu : IsUnit M.det := isUnit_iff_ne_zero.2 hM
  set v₁ : Fin p → ℝ := fun j => v (Sum.inl j)
  set x : Fin p ⊕ Unit → ℝ :=
    Sum.elim (-(M⁻¹ *ᵥ v₁)) fun _ => (v (Sum.inr ()) - c ⬝ᵥ (M⁻¹ *ᵥ v₁)) / q
  have hAx : A *ᵥ x = v := by
    rw [hAdef, fromBlocks_mulVec]
    funext k
    rcases k with j | ⟨⟩
    · simp only [Sum.elim_inl, Matrix.zero_mulVec, add_zero, x, Function.comp_def,
        Matrix.neg_mulVec, Matrix.mulVec_neg, neg_neg]
      rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hMu, Matrix.one_mulVec]
    · simp only [Sum.elim_inr, Pi.add_apply, Matrix.mulVec, dotProduct, Matrix.of_apply,
        Finset.univ_unique, Finset.sum_singleton, x, Function.comp_apply, Sum.elim_inl,
        Pi.neg_apply, neg_mul_neg]
      rw [mul_div_cancel₀ _ hq]
      ring
  have hx : A⁻¹ *ᵥ v = x := by
    rw [← hAx, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hA, Matrix.one_mulVec]
  rw [hx]
  rfl

end Algebra

/-! ### The population sandwich entry -/

variable {𝒳 : Type*} {p : ℕ} [MeasurableSpace 𝒳]

section Population

variable {ν : Measure (𝒳 × Bool × ℝ)}

/-- **The products of two coordinates of the estimating functions are integrable** for a square
integrable outcome and bounded features: each coordinate at `θ` is bounded by
`weightedEnvConst p B θ 0 (1 + |y|)`. -/
theorem integrable_weightedEstFun_mul [IsFiniteMeasure ν] {φ : 𝒳 → Fin p → ℝ}
    (hφ : Measurable φ) {t : Fin p → ℝ} {B : ℝ} (hB : ∀ x, ‖φ x - t‖ ≤ B)
    (hy : MemLp (fun z : 𝒳 × Bool × ℝ => z.2.2) 2 ν) (a b : Bool)
    (θ θ' : EuclideanSpace ℝ (Fin p ⊕ Unit)) (k l : Fin p ⊕ Unit) :
    Integrable (fun z => weightedEstFun φ t a z θ k * weightedEstFun φ t b z θ' l) ν := by
  set K := weightedEnvConst p B θ 0 with hKdef
  set K' := weightedEnvConst p B θ' 0 with hKdef'
  have hK0 : 0 ≤ K := by rw [hKdef, weightedEnvConst]; positivity
  have hK0' : 0 ≤ K' := by rw [hKdef', weightedEnvConst]; positivity
  have hp : ∀ m, Continuous fun x : EuclideanSpace ℝ (Fin p ⊕ Unit) => x m := fun m =>
    (EuclideanSpace.proj (𝕜 := ℝ) m).continuous
  have hm : Measurable fun z => weightedEstFun φ t a z θ k * weightedEstFun φ t b z θ' l :=
    ((hp k).measurable.comp (measurable_weightedEstFun hφ t a θ)).mul
      ((hp l).measurable.comp (measurable_weightedEstFun hφ t b θ'))
  have hy1 : Integrable (fun z : 𝒳 × Bool × ℝ => z.2.2) ν := hy.integrable one_le_two
  have hy2 : Integrable (fun z : 𝒳 × Bool × ℝ => z.2.2 ^ 2) ν := hy.integrable_sq
  have hbd : Integrable (fun z : 𝒳 × Bool × ℝ => K * K' * (1 + 2 * |z.2.2| + z.2.2 ^ 2)) ν :=
    (((integrable_const 1).add (hy1.abs.const_mul 2)).add hy2).const_mul _
  refine hbd.mono' hm.aestronglyMeasurable (ae_of_all _ fun z => ?_)
  have h1 := (abs_weightedEstJac_le (a := a) (θ₀ := θ) (θ := θ)
    (Metric.mem_closedBall_self le_rfl) le_rfl (hB z.1)).2 k
  have h2 := (abs_weightedEstJac_le (a := b) (θ₀ := θ') (θ := θ')
    (Metric.mem_closedBall_self le_rfl) le_rfl (hB z.1)).2 l
  rw [Real.norm_eq_abs, abs_mul]
  calc |weightedEstFun φ t a z θ k| * |weightedEstFun φ t b z θ' l|
      ≤ (K * (1 + |z.2.2|)) * (K' * (1 + |z.2.2|)) :=
        mul_le_mul h1 h2 (abs_nonneg _) (by positivity)
    _ = K * K' * (1 + 2 * |z.2.2| + z.2.2 ^ 2) := by rw [← sq_abs z.2.2]; ring

/-- **The last diagonal entry of the population sandwich is `σ² = E[IF²]`.** Under bounded
features, the margin condition, `P(A = a) > 0` and a square integrable outcome, the entry
`(A⁻¹ B A⁻ᵀ)_{m m}` of the bread `A` and the meat `B` of the stacked equations at `θ₀` is
`weightedArmVariance`. The inverse bread applied to the estimating function has the influence
function as its last coordinate (`inv_breadMatrix_mulVec_weightedEstFun`). -/
theorem sandwich_weightedEstFun_eq_weightedArmVariance [IsFiniteMeasure ν]
    {φ : 𝒳 → Fin p → ℝ} (hφ : Measurable φ) {t : Fin p → ℝ} {B : ℝ} (hB : ∀ x, ‖φ x - t‖ ≤ B)
    {δ : ℝ} (hδ : 0 < δ) (hmargin : ∀ v : Fin p → ℝ, ‖v‖ = 1 →
      δ ≤ ν.real {z | δ ≤ v ⬝ᵥ (φ z.1 - t)}) {a : Bool} (hq : 0 < ν.real {z | z.2.1 = a})
    (hy : MemLp (fun z : 𝒳 × Bool × ℝ => z.2.2) 2 ν) :
    ((breadMatrix ν (weightedEstJac φ t a) (weightedStackedParam ν φ t a))⁻¹ *
      meatMatrix ν (weightedEstFun φ t a) (weightedStackedParam ν φ t a) *
      ((breadMatrix ν (weightedEstJac φ t a) (weightedStackedParam ν φ t a))⁻¹)ᵀ)
        (Sum.inr ()) (Sum.inr ()) = weightedArmVariance ν φ t a := by
  set θ₀ := weightedStackedParam ν φ t a
  set C := (breadMatrix ν (weightedEstJac φ t a) θ₀)⁻¹
  have h := mul_of_integral_mul_transpose_apply (ν := ν) C C
    (f := fun z => WithLp.ofLp (weightedEstFun φ t a z θ₀))
    (g := fun z => WithLp.ofLp (weightedEstFun φ t a z θ₀))
    (fun k l => integrable_weightedEstFun_mul hφ hB hy a a θ₀ θ₀ k l) (Sum.inr ()) (Sum.inr ())
  rw [show meatMatrix ν (weightedEstFun φ t a) θ₀ =
    Matrix.of fun k l => ∫ z, weightedEstFun φ t a z θ₀ k * weightedEstFun φ t a z θ₀ l ∂ν
    from rfl]
  refine h.trans ?_
  rw [weightedArmVariance]
  congr 1
  funext z
  rw [inv_breadMatrix_mulVec_weightedEstFun hφ hB hδ hmargin hq z, sq]

end Population

/-! ### Consistency of the sandwich estimate -/

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {O : ℕ → Ω → 𝒳 × Bool × ℝ}

/-- **Consistency of the sandwich variance estimator of the weighted arm mean.** Under an
i.i.d. sample, measurable features bounded by `B` around `t`, the margin condition,
`P(A = a) > 0` and a square integrable outcome, `n` times the last diagonal entry of the plug-in
sandwich estimate `sandwichMatrixHat` (evaluated at the stacked estimate `θ̂ₙ`) converges in
probability to the asymptotic variance `σ² = weightedArmVariance` of `√n (m̂ₙ - m₀)`. The
envelopes are those of the normal limit: no fourth moment is needed. -/
theorem sandwichMatrixHat_weighted_tendstoInMeasure [IsProbabilityMeasure P]
    (hO : IsIIDSample O P) {φ : 𝒳 → Fin p → ℝ} (hφ : Measurable φ) {t : Fin p → ℝ} {B : ℝ}
    (hB : ∀ x, ‖φ x - t‖ ≤ B) {δ : ℝ} (hδ : 0 < δ) (hmargin : ∀ v : Fin p → ℝ, ‖v‖ = 1 →
      δ ≤ (P.map (O 0)).real {z | δ ≤ v ⬝ᵥ (φ z.1 - t)}) (a : Bool)
    (hq : 0 < (P.map (O 0)).real {z | z.2.1 = a})
    (hy : MemLp (fun z : 𝒳 × Bool × ℝ => z.2.2) 2 (P.map (O 0))) :
    TendstoInMeasure P (fun (n : ℕ) ω => ((n : ℝ) • sandwichMatrixHat O (weightedEstFun φ t a)
      (weightedEstJac φ t a) (weightedStackedEstimate φ t O a) n ω) (Sum.inr ()) (Sum.inr ()))
      atTop (fun _ => weightedArmVariance (P.map (O 0)) φ t a) := by
  have : IsProbabilityMeasure (P.map (O 0)) :=
    (Measure.isProbabilityMeasure_map_iff (hO.aemeasurable 0)).2 inferInstance
  set ν := P.map (O 0) with hν
  set θ₀ := weightedStackedParam ν φ t a with hθ₀
  have hy1 : Integrable (fun z : 𝒳 × Bool × ℝ => z.2.2) ν := hy.integrable one_le_two
  set K := weightedEnvConst p B θ₀ 1 with hK
  have hG : Integrable (fun z : 𝒳 × Bool × ℝ => (p + 1) * (K * (1 + |z.2.2|)) ^ 2) ν := by
    have hy2 : Integrable (fun z : 𝒳 × Bool × ℝ => z.2.2 ^ 2) ν := hy.integrable_sq
    refine ((((integrable_const 1).add (hy1.abs.const_mul 2)).add hy2).const_mul
      ((p + 1) * K ^ 2)).congr (ae_of_all _ fun z => ?_)
    simp only [Pi.add_apply]
    rw [← sq_abs z.2.2]
    ring
  have h := sandwichMatrixHat_tendstoInMeasure hO zero_lt_one
    (fun θ _ => measurable_weightedEstFun hφ t a θ)
    (fun θ _ k l => measurable_weightedEstJac hφ t a θ k l)
    (ae_of_all _ fun z θ _ => weightedEstFun_hasFDerivAt φ t a z θ)
    (ae_of_all _ fun z k l => (continuous_weightedEstJac φ t a z k l).continuousOn)
    (H := fun z => K * (1 + |z.2.2|)) (((integrable_const 1).add hy1.abs).const_mul K)
    (ae_of_all _ fun z θ hθ k l => (abs_weightedEstJac_le hθ zero_le_one (hB z.1)).1 k l)
    hG (ae_of_all _ fun z θ hθ => norm_weightedEstFun_sq_le hθ zero_le_one (hB z.1))
    (det_breadMatrix_weightedEstJac_ne_zero hφ hB hδ hmargin hq θ₀)
    (weightedStackedEstimate_tendstoInMeasure hO hφ hB hδ hmargin a hq hy1)
    (Sum.inr ()) (Sum.inr ())
  rwa [sandwich_weightedEstFun_eq_weightedArmVariance hφ hB hδ hmargin hq hy] at h

omit [MeasurableSpace 𝒳] [MeasurableSpace Ω] in
/-- **The sandwich entry is a mean of squares**: `n` times the last diagonal entry of the sandwich
estimate is `n⁻¹ ∑ᵢ ((Âₙ⁻¹ ψ(Zᵢ; θ̂ₙ))_m)²` for `n ≥ 1` (whatever `Âₙ`, singular or not). -/
theorem sandwichMatrixHat_weighted_eq_sampleMean (φ : 𝒳 → Fin p → ℝ) (t : Fin p → ℝ)
    (O : ℕ → Ω → 𝒳 × Bool × ℝ) (a : Bool) (n : ℕ) (ω : Ω) :
    ((n : ℝ) • sandwichMatrixHat O (weightedEstFun φ t a) (weightedEstJac φ t a)
      (weightedStackedEstimate φ t O a) n ω) (Sum.inr ()) (Sum.inr ()) =
      sampleMean (fun z => (((breadMatrixHat O (weightedEstJac φ t a)
        (weightedStackedEstimate φ t O a) n ω)⁻¹ *ᵥ WithLp.ofLp (weightedEstFun φ t a z
          (weightedStackedEstimate φ t O a n ω))) (Sum.inr ())) ^ 2) O n ω := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [sampleMean]
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  set C := (breadMatrixHat O (weightedEstJac φ t a) (weightedStackedEstimate φ t O a) n ω)⁻¹
  have h := mul_of_sampleMean_mul_transpose_apply C C
    (fun z => WithLp.ofLp (weightedEstFun φ t a z (weightedStackedEstimate φ t O a n ω)))
    (fun z => WithLp.ofLp (weightedEstFun φ t a z (weightedStackedEstimate φ t O a n ω)))
    O n ω (Sum.inr ()) (Sum.inr ())
  simp only [sandwichMatrixHat, smul_smul, mul_inv_cancel₀ hn0, one_smul]
  simp only [sq]
  exact h

omit [MeasurableSpace 𝒳] [MeasurableSpace Ω] in
/-- **The sandwich entry is nonnegative** for every sample and every sample size. -/
theorem sandwichMatrixHat_weighted_nonneg (φ : 𝒳 → Fin p → ℝ) (t : Fin p → ℝ)
    (O : ℕ → Ω → 𝒳 × Bool × ℝ) (a : Bool) (n : ℕ) (ω : Ω) :
    0 ≤ ((n : ℝ) • sandwichMatrixHat O (weightedEstFun φ t a) (weightedEstJac φ t a)
      (weightedStackedEstimate φ t O a) n ω) (Sum.inr ()) (Sum.inr ()) := by
  rw [sandwichMatrixHat_weighted_eq_sampleMean]
  exact mul_nonneg (inv_nonneg.2 (Nat.cast_nonneg n))
    (Finset.sum_nonneg fun i _ => sq_nonneg _)

/-! ### The explicit form -/

section Explicit

omit [MeasurableSpace 𝒳] [MeasurableSpace Ω]

/-- The **empirical tilted second moment matrix** at the sample tilt,
`M̂ = n⁻¹ ∑ᵢ ŵ(Xᵢ) (φ(Xᵢ) - t)(φ(Xᵢ) - t)ᵀ` with `ŵ = w_{β̂ₙ}`. -/
noncomputable def sampleTiltedSecondMoment (φ : 𝒳 → Fin p → ℝ) (t : Fin p → ℝ)
    (O : ℕ → Ω → 𝒳 × Bool × ℝ) (n : ℕ) (ω : Ω) : Matrix (Fin p) (Fin p) ℝ :=
  Matrix.of fun j k => sampleMean (fun z => tiltWeight φ t 0 (sampleTilt φ t O n ω) z.1 *
    (φ z.1 j - t j) * (φ z.1 k - t k)) O n ω

/-- The **empirical coupling vector** `ĉ = n⁻¹ ∑ᵢ 1{Aᵢ = a} ŵ(Xᵢ) (Yᵢ - m̂ₙ) (φ(Xᵢ) - t)`. -/
noncomputable def sampleWeightedCoupling (φ : 𝒳 → Fin p → ℝ) (t : Fin p → ℝ)
    (O : ℕ → Ω → 𝒳 × Bool × ℝ) (a : Bool) (n : ℕ) (ω : Ω) : Fin p → ℝ :=
  fun k => sampleMean (fun z => armIndObs a z * tiltWeight φ t 0 (sampleTilt φ t O n ω) z.1 *
    (z.2.2 - sampleBalancedArmMean φ t O a n ω) * (φ z.1 k - t k)) O n ω

/-- The **empirical tilted mass of the arm** `q̂ = n⁻¹ ∑ᵢ 1{Aᵢ = a} ŵ(Xᵢ)`. -/
noncomputable def sampleWeightedArmMass (φ : 𝒳 → Fin p → ℝ) (t : Fin p → ℝ)
    (O : ℕ → Ω → 𝒳 × Bool × ℝ) (a : Bool) (n : ℕ) (ω : Ω) : ℝ :=
  sampleMean (fun z => armIndObs a z * tiltWeight φ t 0 (sampleTilt φ t O n ω) z.1) O n ω

/-- The **estimated influence value** of a record `z = (x, s, y)`:
`ÎF(z) = (1{s = a} ŵ(x) (y - m̂ₙ) - ĉᵀ M̂⁻¹ ŵ(x) (φ(x) - t)) / q̂`, the influence function
`weightedArmInfluence` with the population tilt, arm mean, coupling, second moment and mass
replaced by their estimates. -/
noncomputable def sampleWeightedArmInfluence (φ : 𝒳 → Fin p → ℝ) (t : Fin p → ℝ)
    (O : ℕ → Ω → 𝒳 × Bool × ℝ) (a : Bool) (n : ℕ) (ω : Ω) (z : 𝒳 × Bool × ℝ) : ℝ :=
  (armIndObs a z * tiltWeight φ t 0 (sampleTilt φ t O n ω) z.1 *
      (z.2.2 - sampleBalancedArmMean φ t O a n ω) -
    sampleWeightedCoupling φ t O a n ω ⬝ᵥ ((sampleTiltedSecondMoment φ t O n ω)⁻¹ *ᵥ
      fun j => tiltWeight φ t 0 (sampleTilt φ t O n ω) z.1 * (φ z.1 j - t j))) /
    sampleWeightedArmMass φ t O a n ω

/-- The **explicit variance estimate** `σ̂ₙ² = n⁻¹ ∑ᵢ ÎF(Zᵢ)²`. -/
noncomputable def sampleWeightedArmVariance (φ : 𝒳 → Fin p → ℝ) (t : Fin p → ℝ)
    (O : ℕ → Ω → 𝒳 × Bool × ℝ) (a : Bool) (n : ℕ) (ω : Ω) : ℝ :=
  sampleMean (fun z => sampleWeightedArmInfluence φ t O a n ω z ^ 2) O n ω

/-- **The empirical bread is block lower triangular**: `Âₙ = [[-M̂, 0], [-ĉᵀ, q̂]]`. -/
theorem breadMatrixHat_weightedEstJac (φ : 𝒳 → Fin p → ℝ) (t : Fin p → ℝ)
    (O : ℕ → Ω → 𝒳 × Bool × ℝ) (a : Bool) (n : ℕ) (ω : Ω) :
    breadMatrixHat O (weightedEstJac φ t a) (weightedStackedEstimate φ t O a) n ω =
      Matrix.fromBlocks (-sampleTiltedSecondMoment φ t O n ω) 0
        (Matrix.of fun _ k => -sampleWeightedCoupling φ t O a n ω k)
        (Matrix.of fun _ _ => sampleWeightedArmMass φ t O a n ω) := by
  ext k l
  rcases k with j | u <;> rcases l with k | v <;>
    simp [breadMatrixHat, weightedEstJac, sampleTiltedSecondMoment, sampleWeightedCoupling,
      sampleWeightedArmMass, sampleMean, weightedStackedEstimate, Finset.sum_neg_distrib]

/-- **The sandwich entry in explicit form.** When the empirical tilted second moment matrix `M̂`
is nonsingular and the empirical tilted mass `q̂` of the arm is not zero, `n` times the last
diagonal entry of the sandwich estimate is the empirical mean of the squared estimated influence
values, `n⁻¹ ∑ᵢ ÎF(Zᵢ)²`. Where the empirical bread is singular the sandwich uses the zero
inverse and the two differ; that event has probability tending to zero. -/
theorem sandwichMatrixHat_weighted_eq_sampleWeightedArmVariance (φ : 𝒳 → Fin p → ℝ)
    (t : Fin p → ℝ) (O : ℕ → Ω → 𝒳 × Bool × ℝ) (a : Bool) {n : ℕ} {ω : Ω}
    (hM : (sampleTiltedSecondMoment φ t O n ω).det ≠ 0)
    (hq : sampleWeightedArmMass φ t O a n ω ≠ 0) :
    ((n : ℝ) • sandwichMatrixHat O (weightedEstFun φ t a) (weightedEstJac φ t a)
      (weightedStackedEstimate φ t O a) n ω) (Sum.inr ()) (Sum.inr ()) =
      sampleWeightedArmVariance φ t O a n ω := by
  rw [sandwichMatrixHat_weighted_eq_sampleMean, breadMatrixHat_weightedEstJac,
    sampleWeightedArmVariance]
  congr 1
  funext z
  rw [inv_fromBlocks_mulVec_inr hM hq]
  rfl

/-- The **cross covariance estimate** of the influence values of two arms `a` and `b`:
`((Â_a)⁻¹ Ĉ (Â_b)⁻ᵀ)_{m m}` with the empirical breads of the two stacked systems and the cross
meat `Ĉ = n⁻¹ ∑ᵢ ψ_a(Zᵢ; θ̂_a) ψ_b(Zᵢ; θ̂_b)ᵀ`. For `a = b` it is the sandwich entry
(`weightedInfluenceCovHat_self`). -/
noncomputable def weightedInfluenceCovHat (φ : 𝒳 → Fin p → ℝ) (t : Fin p → ℝ)
    (O : ℕ → Ω → 𝒳 × Bool × ℝ) (a b : Bool) (n : ℕ) (ω : Ω) : ℝ :=
  ((breadMatrixHat O (weightedEstJac φ t a) (weightedStackedEstimate φ t O a) n ω)⁻¹ *
    Matrix.of (fun k l => sampleMean (fun z =>
      weightedEstFun φ t a z (weightedStackedEstimate φ t O a n ω) k *
        weightedEstFun φ t b z (weightedStackedEstimate φ t O b n ω) l) O n ω) *
    ((breadMatrixHat O (weightedEstJac φ t b) (weightedStackedEstimate φ t O b) n ω)⁻¹)ᵀ)
      (Sum.inr ()) (Sum.inr ())

/-- The cross covariance estimate is the empirical mean of the products of the estimated
influence values `(Âₐ⁻¹ ψₐ(Zᵢ; θ̂ₐ))_m` of the two arms. -/
theorem weightedInfluenceCovHat_eq_sampleMean (φ : 𝒳 → Fin p → ℝ) (t : Fin p → ℝ)
    (O : ℕ → Ω → 𝒳 × Bool × ℝ) (a b : Bool) (n : ℕ) (ω : Ω) :
    weightedInfluenceCovHat φ t O a b n ω = sampleMean (fun z =>
      ((breadMatrixHat O (weightedEstJac φ t a) (weightedStackedEstimate φ t O a) n ω)⁻¹ *ᵥ
        WithLp.ofLp (weightedEstFun φ t a z (weightedStackedEstimate φ t O a n ω)))
          (Sum.inr ()) *
      ((breadMatrixHat O (weightedEstJac φ t b) (weightedStackedEstimate φ t O b) n ω)⁻¹ *ᵥ
        WithLp.ofLp (weightedEstFun φ t b z (weightedStackedEstimate φ t O b n ω)))
          (Sum.inr ())) O n ω :=
  mul_of_sampleMean_mul_transpose_apply _ _ _ _ O n ω _ _

/-- The diagonal of the cross covariance estimate is the sandwich entry. -/
theorem weightedInfluenceCovHat_self (φ : 𝒳 → Fin p → ℝ) (t : Fin p → ℝ)
    (O : ℕ → Ω → 𝒳 × Bool × ℝ) (a : Bool) (n : ℕ) (ω : Ω) :
    weightedInfluenceCovHat φ t O a a n ω =
      ((n : ℝ) • sandwichMatrixHat O (weightedEstFun φ t a) (weightedEstJac φ t a)
        (weightedStackedEstimate φ t O a) n ω) (Sum.inr ()) (Sum.inr ()) := by
  rw [weightedInfluenceCovHat_eq_sampleMean, sandwichMatrixHat_weighted_eq_sampleMean]
  simp only [sq]

end Explicit

/-- **The empirical bread is nonsingular with probability tending to one**, under the
hypotheses of the normal limit. -/
theorem withProbTendingToOne_det_breadMatrixHat_ne_zero [IsProbabilityMeasure P]
    (hO : IsIIDSample O P) {φ : 𝒳 → Fin p → ℝ} (hφ : Measurable φ) {t : Fin p → ℝ} {B : ℝ}
    (hB : ∀ x, ‖φ x - t‖ ≤ B) {δ : ℝ} (hδ : 0 < δ) (hmargin : ∀ v : Fin p → ℝ, ‖v‖ = 1 →
      δ ≤ (P.map (O 0)).real {z | δ ≤ v ⬝ᵥ (φ z.1 - t)}) (a : Bool)
    (hq : 0 < (P.map (O 0)).real {z | z.2.1 = a})
    (hy : Integrable (fun z : 𝒳 × Bool × ℝ => z.2.2) (P.map (O 0))) :
    WithProbTendingToOne P (fun n => {ω |
      (breadMatrixHat O (weightedEstJac φ t a) (weightedStackedEstimate φ t O a) n ω).det ≠ 0})
    := by
  have : IsProbabilityMeasure (P.map (O 0)) :=
    (Measure.isProbabilityMeasure_map_iff (hO.aemeasurable 0)).2 inferInstance
  set ν := P.map (O 0) with hν
  set θ₀ := weightedStackedParam ν φ t a with hθ₀
  set A := breadMatrix ν (weightedEstJac φ t a) θ₀ with hA
  set K := weightedEnvConst p B θ₀ 1 with hK
  have h1 := breadMatrixHat_tendstoInMeasure hO zero_lt_one
    (fun θ _ k l => measurable_weightedEstJac hφ t a θ k l)
    (ae_of_all _ fun z k l => (continuous_weightedEstJac φ t a z k l).continuousOn)
    (H := fun z => K * (1 + |z.2.2|)) (((integrable_const 1).add hy.abs).const_mul K)
    (ae_of_all _ fun z θ hθ k l => (abs_weightedEstJac_le hθ zero_le_one (hB z.1)).1 k l)
    (weightedStackedEstimate_tendstoInMeasure hO hφ hB hδ hmargin a hq hy)
  have h1' : TendstoInMeasure P (fun n ω => (fun k l =>
      breadMatrixHat O (weightedEstJac φ t a) (weightedStackedEstimate φ t O a) n ω k l :
        Fin p ⊕ Unit → Fin p ⊕ Unit → ℝ)) atTop (fun _ => Matrix.of.symm A) :=
    tendstoInMeasure_pi (X := fun k n ω l =>
      breadMatrixHat O (weightedEstJac φ t a) (weightedStackedEstimate φ t O a) n ω k l)
      fun k => tendstoInMeasure_pi (X := fun l n ω =>
        breadMatrixHat O (weightedEstJac φ t a) (weightedStackedEstimate φ t O a) n ω k l)
        fun l => h1 k l
  have hdet : Continuous fun F : Fin p ⊕ Unit → Fin p ⊕ Unit → ℝ => (Matrix.of F).det :=
    (continuous_id : Continuous fun F : Fin p ⊕ Unit → Fin p ⊕ Unit → ℝ =>
      (Matrix.of F : Matrix (Fin p ⊕ Unit) (Fin p ⊕ Unit) ℝ)).matrix_det
  have h2 := h1'.comp_continuousAt hdet.continuousAt
  have hA0 : A.det ≠ 0 := det_breadMatrix_weightedEstJac_ne_zero hφ hB hδ hmargin hq θ₀
  refine (h2.withProbTendingToOne_dist_lt (abs_pos.2 hA0)).mono fun n ω hω => ?_
  simp only [Set.mem_ofPred_eq, Real.dist_eq] at hω ⊢
  intro h0
  have : (Matrix.of fun k l =>
      breadMatrixHat O (weightedEstJac φ t a) (weightedStackedEstimate φ t O a) n ω k l) =
      breadMatrixHat O (weightedEstJac φ t a) (weightedStackedEstimate φ t O a) n ω := rfl
  rw [this, h0, zero_sub, abs_neg] at hω
  exact lt_irrefl _ hω

/-- **Consistency of the explicit variance estimate** `n⁻¹ ∑ᵢ ÎF(Zᵢ)²`, under the hypotheses of
`sandwichMatrixHat_weighted_tendstoInMeasure`: it agrees with the sandwich entry on the event
that the empirical bread is nonsingular, whose probability tends to one. -/
theorem sampleWeightedArmVariance_tendstoInMeasure [IsProbabilityMeasure P]
    (hO : IsIIDSample O P) {φ : 𝒳 → Fin p → ℝ} (hφ : Measurable φ) {t : Fin p → ℝ} {B : ℝ}
    (hB : ∀ x, ‖φ x - t‖ ≤ B) {δ : ℝ} (hδ : 0 < δ) (hmargin : ∀ v : Fin p → ℝ, ‖v‖ = 1 →
      δ ≤ (P.map (O 0)).real {z | δ ≤ v ⬝ᵥ (φ z.1 - t)}) (a : Bool)
    (hq : 0 < (P.map (O 0)).real {z | z.2.1 = a})
    (hy : MemLp (fun z : 𝒳 × Bool × ℝ => z.2.2) 2 (P.map (O 0))) :
    TendstoInMeasure P (sampleWeightedArmVariance φ t O a) atTop
      (fun _ => weightedArmVariance (P.map (O 0)) φ t a) := by
  refine (sandwichMatrixHat_weighted_tendstoInMeasure hO hφ hB hδ hmargin a hq
    hy).congr_withProbTendingToOne (withProbTendingToOne_det_breadMatrixHat_ne_zero hO hφ hB hδ
      hmargin a hq (hy.integrable one_le_two)) fun n ω hω => ?_
  simp only [Set.mem_ofPred_eq] at hω
  rw [breadMatrixHat_weightedEstJac, det_fromBlocks_bread] at hω
  exact sandwichMatrixHat_weighted_eq_sampleWeightedArmVariance φ t O a
    (fun h => hω (by rw [h]; ring)) (fun h => hω (by rw [h]; ring))

end PopulationAdjustment

end CausalInference
