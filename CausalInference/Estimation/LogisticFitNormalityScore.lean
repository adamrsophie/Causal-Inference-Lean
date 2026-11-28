/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.Estimation.PosteriorLimitLogistic
public import CausalInference.Estimation.VectorZEstimator

/-!
# The logistic score: moments, derivative and information

For records `(c, y)` of the logistic model with design `z`, the score of the log density in the
coefficient, written in Euclidean coordinates, is the estimating function

  `ψ((c, y), θ) = s_y(z(c) ⬝ θ) z(c)`,  `s_y(η) = 1[y = 1] - σ(η)`

(`logisticEstFun`), with derivative `J((c, y), θ) = -w(z(c) ⬝ θ) z(c) z(c)ᵀ`, `w = σ (1 - σ)`
(`logisticEstJac`, `hasFDerivAt_logisticEstFun`).

Under the law `P_{ξ₀}` of the logistic family of records with regressor law `R`, an integral is
an average over `R` of the two outcome values weighted by `1 - σ` and `σ`
(`integral_logisticFamily_law`). Hence:

* the score has mean zero at the true coefficient (`integral_logisticEstFun_eq_zero`);
* its second moment matrix, the meat, is the information `I(ξ₀) = ∫ w z zᵀ dR`
  (`meatMatrix_logisticEstFun`);
* minus the mean of the derivative, the bread, is also `I(ξ₀)` (`breadMatrix_logisticEstJac`),
  so the sandwich `A⁻¹ B A⁻ᵀ` is `I(ξ₀)⁻¹` (`sandwich_logisticInfo`);
* for a design bounded by `B` the derivative is bounded by `B²` entrywise
  (`abs_logisticEstJac_le`) and the score is square integrable.

## Main definitions

* `PosteriorLimit.logisticEstFun`, `PosteriorLimit.logisticEstJac`.

## Main results

* `hasFDerivAt_logisticEstFun`, `integral_logisticFamily_law`,
  `integral_logisticEstFun_eq_zero`, `meatMatrix_logisticEstFun`, `breadMatrix_logisticEstJac`,
  `sandwich_logisticInfo`.

## References

* P. McCullagh and J. A. Nelder, *Generalized Linear Models*, 2nd edition, Chapman and Hall
  (1989), chapter 4.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology Set Matrix
open scoped ENNReal NNReal

namespace CausalInference

namespace PosteriorLimit

open PopulationAdjustment PopulationAdjustment.BayesStandardization

variable {C κ : Type*} [Fintype κ]

/-! ### The estimating function and its derivative -/

/-- The **logistic estimating function** in Euclidean coordinates:
`ψ((c, y), θ) = (1[y = 1] - σ(z(c) ⬝ θ)) z(c)`, the score of one record. -/
noncomputable def logisticEstFun (z : C → κ → ℝ) (q : C × ℝ) (θ : EuclideanSpace ℝ κ) :
    EuclideanSpace ℝ κ :=
  WithLp.toLp 2 (logisticDensScore (z q.1 ⬝ᵥ WithLp.ofLp θ) q.2 • z q.1)

/-- The **derivative of the logistic estimating function**: the matrix
`-w(z(c) ⬝ θ) z(c) z(c)ᵀ`. -/
noncomputable def logisticEstJac (z : C → κ → ℝ) (q : C × ℝ) (θ : EuclideanSpace ℝ κ) :
    Matrix κ κ ℝ :=
  Matrix.of fun i j ↦ -(sigmoidWeight (z q.1 ⬝ᵥ WithLp.ofLp θ) * z q.1 i * z q.1 j)

lemma logisticEstFun_apply (z : C → κ → ℝ) (q : C × ℝ) (θ : EuclideanSpace ℝ κ) (i : κ) :
    logisticEstFun z q θ i = logisticDensScore (z q.1 ⬝ᵥ WithLp.ofLp θ) q.2 * z q.1 i := rfl

/-- The derivative of the score in the linear predictor is minus the weight. -/
lemma hasDerivAt_logisticDensScore (η y : ℝ) :
    HasDerivAt (fun t ↦ logisticDensScore t y) (-sigmoidWeight η) η := by
  have h := (Real.hasDerivAt_sigmoid η).const_sub (if y = 1 then (1 : ℝ) else 0)
  simpa [logisticDensScore, sigmoidWeight] using h

/-- **The derivative of the logistic estimating function** is the matrix `logisticEstJac`. -/
theorem hasFDerivAt_logisticEstFun [DecidableEq κ] (z : C → κ → ℝ) (q : C × ℝ)
    (θ : EuclideanSpace ℝ κ) :
    HasFDerivAt (logisticEstFun z q) (Matrix.toEuclideanCLM (𝕜 := ℝ) (logisticEstJac z q θ))
      θ := by
  set L : EuclideanSpace ℝ κ →L[ℝ] ℝ :=
    (designCLM (z q.1)).comp (PiLp.continuousLinearEquiv 2 ℝ fun _ : κ ↦ ℝ).toContinuousLinearMap
    with hL
  have hLapp : ∀ θ', L θ' = z q.1 ⬝ᵥ WithLp.ofLp θ' := fun θ' ↦ by
    simp only [hL, ContinuousLinearMap.coe_comp, Function.comp_apply, designCLM_apply]
    rfl
  have hlin : HasFDerivAt (fun θ' : EuclideanSpace ℝ κ ↦ z q.1 ⬝ᵥ WithLp.ofLp θ') L θ := by
    have : (fun θ' : EuclideanSpace ℝ κ ↦ z q.1 ⬝ᵥ WithLp.ofLp θ') = ⇑L := funext fun θ' ↦
      (hLapp θ').symm
    rw [this]
    exact L.hasFDerivAt
  have h2 := ((hasDerivAt_logisticDensScore (z q.1 ⬝ᵥ WithLp.ofLp θ) q.2).comp_hasFDerivAt θ
    hlin).smul_const (WithLp.toLp 2 (z q.1) : EuclideanSpace ℝ κ)
  have hfun : logisticEstFun z q = fun θ' ↦ ((fun t ↦ logisticDensScore t q.2) ∘
      fun θ' : EuclideanSpace ℝ κ ↦ z q.1 ⬝ᵥ WithLp.ofLp θ') θ' •
        (WithLp.toLp 2 (z q.1) : EuclideanSpace ℝ κ) := by
    funext θ'
    exact WithLp.toLp_smul 2 _ _
  rw [hfun]
  refine h2.congr_fderiv ?_
  ext v i
  simp only [ContinuousLinearMap.smulRight_apply, smul_apply, smul_eq_mul,
    hLapp, PiLp.smul_apply, ofLp_toEuclideanCLM, logisticEstJac, mulVec,
    dotProduct, Matrix.of_apply]
  simp only [Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  ring

/-! ### Integrals under the logistic family -/

section Law

variable [MeasurableSpace C] {R : Measure C} [IsProbabilityMeasure R] {z : C → κ → ℝ}
  {hz : ∀ j, Measurable fun c ↦ z c j}

lemma logisticDens_zero (η : ℝ) : logisticDens η 0 = 1 - Real.sigmoid η := by
  simp [logisticDens]

lemma logisticDens_one (η : ℝ) : logisticDens η 1 = Real.sigmoid η := by
  simp [logisticDens]

/-- **Integrals under the logistic family of records.** For `f` integrable under `P_{ξ₀}`,
`∫ f dP_{ξ₀} = ∫ ((1 - σ(z(c) ⬝ ξ₀)) f(c, 0) + σ(z(c) ⬝ ξ₀) f(c, 1)) dR(c)`. -/
theorem integral_logisticFamily_law {ξ₀ : κ → ℝ} {f : C × ℝ → ℝ}
    (hf : Integrable f ((glmFamily logisticKernel R z hz).law ξ₀)) :
    ∫ q, f q ∂(glmFamily logisticKernel R z hz).law ξ₀ =
      ∫ c, ((1 - Real.sigmoid (z c ⬝ᵥ ξ₀)) * f (c, 0) + Real.sigmoid (z c ⬝ᵥ ξ₀) * f (c, 1))
        ∂R := by
  set F := glmFamily logisticKernel R z hz
  have hi := (ParametricFamily.integrable_law_iff (F := F) (Set.mem_univ ξ₀)).1 hf
  rw [ParametricFamily.integral_law (Set.mem_univ ξ₀)]
  change ∫ q, logisticDens (z q.1 ⬝ᵥ ξ₀) q.2 * f q ∂(R.prod
    (Measure.dirac 0 + Measure.dirac 1)) = _
  change Integrable (fun q ↦ logisticDens (z q.1 ⬝ᵥ ξ₀) q.2 * f q)
    (R.prod (Measure.dirac 0 + Measure.dirac 1)) at hi
  rw [integral_prod _ hi]
  refine integral_congr_ae (ae_of_all _ fun c ↦ ?_)
  simp only
  rw [integral_add_measure (integrable_dirac eNorm_lt_top) (integrable_dirac eNorm_lt_top),
    integral_dirac, integral_dirac, logisticDens_zero, logisticDens_one]

/-- Almost sure properties of the design under the regressor law hold under the logistic family
of records. -/
lemma ae_logisticFamily_law_of_ae {p : C → Prop}
    (h : ∀ᵐ c ∂R, p c) {ξ₀ : κ → ℝ} :
    ∀ᵐ q ∂(glmFamily logisticKernel R z hz).law ξ₀, p q.1 := by
  refine (withDensity_absolutelyContinuous _ _).ae_le ?_
  change ∀ᵐ q ∂(R.prod (Measure.dirac (0 : ℝ) + Measure.dirac 1)), p q.1
  rw [ae_iff] at h ⊢
  have hS : {q : C × ℝ | ¬ p q.1} = {c | ¬ p c} ×ˢ (Set.univ : Set ℝ) := by ext; simp
  rw [hS, Measure.prod_prod, h, zero_mul]

lemma abs_logisticDensScore_le (η y : ℝ) : |logisticDensScore η y| ≤ 1 := by
  have h0 := Real.sigmoid_pos η
  have h1 := Real.sigmoid_lt_one η
  unfold logisticDensScore
  split_ifs <;> rw [abs_le] <;> constructor <;> linarith

lemma measurable_logisticDensScore : Measurable fun p : ℝ × ℝ ↦ logisticDensScore p.1 p.2 := by
  unfold logisticDensScore
  exact (Measurable.ite (measurableSet_eq_fun measurable_snd measurable_const) measurable_const
    measurable_const).sub (continuous_sigmoid.measurable.comp measurable_fst)

lemma measurable_logisticDensScore_design (hz : ∀ j, Measurable fun c ↦ z c j) (ξ : κ → ℝ) :
    Measurable fun q : C × ℝ ↦ logisticDensScore (z q.1 ⬝ᵥ ξ) q.2 :=
  measurable_logisticDensScore.comp
    (((measurable_dotProduct_design hz ξ).comp measurable_fst).prodMk measurable_snd)


/-- A measurable function bounded almost surely under a probability law is integrable. -/
lemma integrable_of_ae_abs_le {α : Type*} [MeasurableSpace α] {ρ : Measure α}
    [IsFiniteMeasure ρ] {f : α → ℝ} (hf : Measurable f) {M : ℝ} (h : ∀ᵐ x ∂ρ, |f x| ≤ M) :
    Integrable f ρ :=
  Integrable.of_bound hf.aestronglyMeasurable M (h.mono fun x hx ↦ by rwa [Real.norm_eq_abs])

variable {ξ₀ : κ → ℝ} {B : ℝ}

/-- Under the logistic family with a design bounded by `B` under `R`, the design is bounded by
`max B 0` almost surely. -/
lemma ae_abs_design_le (hB : ∀ᵐ c ∂R, ∀ j, |z c j| ≤ B) :
    ∀ᵐ q ∂(glmFamily logisticKernel R z hz).law ξ₀, ∀ j, |z q.1 j| ≤ max B 0 :=
  ae_logisticFamily_law_of_ae (p := fun c ↦ ∀ j, |z c j| ≤ max B 0)
    (hB.mono fun _ hc j ↦ (hc j).trans (le_max_left _ _))

lemma abs_mul_le_of_abs_le {a b c d B : ℝ} (hB : 0 ≤ B) (ha : |a| ≤ 1) (hb : |b| ≤ 1)
    (hc : |c| ≤ B) (hd : |d| ≤ B) : |a * b * c * d| ≤ B ^ 2 := by
  rw [abs_mul, abs_mul, abs_mul]
  calc |a| * |b| * |c| * |d| ≤ 1 * 1 * B * B := by gcongr
    _ = B ^ 2 := by ring

/-- **The score has mean zero at the true coefficient**: `∫ ψ(·, ξ₀) dP_{ξ₀} = 0`. -/
theorem integral_logisticEstFun_eq_zero (hB : ∀ᵐ c ∂R, ∀ j, |z c j| ≤ B) :
    ∫ q, logisticEstFun z q (WithLp.toLp 2 ξ₀) ∂(glmFamily logisticKernel R z hz).law ξ₀ = 0 := by
  have := ParametricFamily.isProbabilityMeasure_law (F := glmFamily logisticKernel R z hz)
    (Set.mem_univ ξ₀)
  have hint : ∀ i, Integrable (fun q ↦ logisticEstFun z q (WithLp.toLp 2 ξ₀) i)
      ((glmFamily logisticKernel R z hz).law ξ₀) := fun i ↦ by
    refine integrable_of_ae_abs_le ((measurable_logisticDensScore_design hz ξ₀).mul
      ((hz i).comp measurable_fst)) (M := max B 0) ((ae_abs_design_le hB).mono fun q hq ↦ ?_)
    rw [logisticEstFun_apply, WithLp.ofLp_toLp, abs_mul]
    calc |logisticDensScore (z q.1 ⬝ᵥ ξ₀) q.2| * |z q.1 i| ≤ 1 * max B 0 :=
          mul_le_mul (abs_logisticDensScore_le _ _) (hq i) (abs_nonneg _) zero_le_one
      _ = max B 0 := one_mul _
  ext i
  rw [eval_integral_piLp hint i, integral_logisticFamily_law (hint i)]
  simp only [logisticEstFun_apply, logisticDensScore, PiLp.zero_apply]
  norm_num
  refine integral_eq_zero_of_ae (ae_of_all _ fun c ↦ ?_)
  simp only [Pi.zero_apply]
  ring

/-- Entrywise integrability of the products of the score and of the derivative. -/
lemma integrable_logisticEstFun_mul (hB : ∀ᵐ c ∂R, ∀ j, |z c j| ≤ B) (i j : κ) :
    Integrable (fun q ↦ logisticEstFun z q (WithLp.toLp 2 ξ₀) i *
      logisticEstFun z q (WithLp.toLp 2 ξ₀) j) ((glmFamily logisticKernel R z hz).law ξ₀) := by
  have := ParametricFamily.isProbabilityMeasure_law (F := glmFamily logisticKernel R z hz)
    (Set.mem_univ ξ₀)
  have hs := measurable_logisticDensScore_design hz ξ₀
  refine integrable_of_ae_abs_le (((hs.mul ((hz i).comp measurable_fst))).mul
    (hs.mul ((hz j).comp measurable_fst))) (M := (max B 0) ^ 2)
    ((ae_abs_design_le hB).mono fun q hq ↦ ?_)
  simp only [logisticEstFun_apply]
  have e : logisticDensScore (z q.1 ⬝ᵥ ξ₀) q.2 * z q.1 i *
      (logisticDensScore (z q.1 ⬝ᵥ ξ₀) q.2 * z q.1 j) =
      logisticDensScore (z q.1 ⬝ᵥ ξ₀) q.2 * logisticDensScore (z q.1 ⬝ᵥ ξ₀) q.2 * z q.1 i *
        z q.1 j := by ring
  rw [e]
  exact abs_mul_le_of_abs_le (le_max_right _ _) (abs_logisticDensScore_le _ _)
    (abs_logisticDensScore_le _ _) (hq i) (hq j)

/-- **The meat is the information**: `∫ ψ ψᵀ dP_{ξ₀} = I(ξ₀)` at the true coefficient. -/
theorem meatMatrix_logisticEstFun (hB : ∀ᵐ c ∂R, ∀ j, |z c j| ≤ B) :
    meatMatrix ((glmFamily logisticKernel R z hz).law ξ₀) (logisticEstFun z)
      (WithLp.toLp 2 ξ₀) = logisticInfo R z ξ₀ := by
  ext i j
  simp only [meatMatrix, Matrix.of_apply]
  rw [integral_logisticFamily_law (integrable_logisticEstFun_mul hB i j), logisticInfo,
    Matrix.of_apply]
  refine integral_congr_ae (ae_of_all _ fun c ↦ ?_)
  simp only [logisticEstFun_apply, logisticDensScore, sigmoidWeight]
  norm_num
  ring

/-- **The bread is the information**: `-∫ J(·, ξ₀) dP_{ξ₀} = I(ξ₀)`. -/
theorem breadMatrix_logisticEstJac (hB : ∀ᵐ c ∂R, ∀ j, |z c j| ≤ B) :
    breadMatrix ((glmFamily logisticKernel R z hz).law ξ₀) (logisticEstJac z)
      (WithLp.toLp 2 ξ₀) = logisticInfo R z ξ₀ := by
  have := ParametricFamily.isProbabilityMeasure_law (F := glmFamily logisticKernel R z hz)
    (Set.mem_univ ξ₀)
  have hzm : Measurable z := measurable_pi_iff.2 hz
  ext i j
  have hi : Integrable (fun q : C × ℝ ↦ logisticEstJac z q (WithLp.toLp 2 ξ₀) i j)
      ((glmFamily logisticKernel R z hz).law ξ₀) := by
    refine integrable_of_ae_abs_le ((((measurable_sigmoidWeight_dotProduct hzm ξ₀).mul
      ((hz i))).mul (hz j)).comp measurable_fst).neg (M := (max B 0) ^ 2)
      ((ae_abs_design_le hB).mono fun q hq ↦ ?_)
    simp only [logisticEstJac, Matrix.of_apply, abs_neg]
    have h1 : |sigmoidWeight (z q.1 ⬝ᵥ ξ₀)| ≤ 1 := by
      rw [abs_of_pos (sigmoidWeight_pos _)]; exact sigmoidWeight_le_one _
    have := abs_mul_le_of_abs_le (le_max_right B 0) h1 (abs_one.le) (hq i) (hq j)
    simpa using this
  simp only [breadMatrix, Matrix.of_apply]
  rw [integral_logisticFamily_law hi, logisticInfo, Matrix.of_apply, ← integral_neg]
  refine integral_congr_ae (ae_of_all _ fun c ↦ ?_)
  simp only [logisticEstJac, Matrix.of_apply]
  ring

/-- **The sandwich is the inverse information** when the information is positive definite:
`A⁻¹ B A⁻ᵀ = I(ξ₀)⁻¹` with bread and meat both equal to `I(ξ₀)`. -/
theorem sandwich_logisticInfo [DecidableEq κ] (hB : ∀ᵐ c ∂R, ∀ j, |z c j| ≤ B)
    (hI : (logisticInfo R z ξ₀).PosDef) :
    (breadMatrix ((glmFamily logisticKernel R z hz).law ξ₀) (logisticEstJac z)
        (WithLp.toLp 2 ξ₀))⁻¹ *
      meatMatrix ((glmFamily logisticKernel R z hz).law ξ₀) (logisticEstFun z)
        (WithLp.toLp 2 ξ₀) *
      ((breadMatrix ((glmFamily logisticKernel R z hz).law ξ₀) (logisticEstJac z)
        (WithLp.toLp 2 ξ₀))⁻¹)ᵀ = (logisticInfo R z ξ₀)⁻¹ := by
  rw [breadMatrix_logisticEstJac hB, meatMatrix_logisticEstFun hB]
  have hsymm : (logisticInfo R z ξ₀)ᵀ = logisticInfo R z ξ₀ := by
    have := hI.isHermitian
    rwa [IsHermitian, conjTranspose_eq_transpose_of_trivial] at this
  rw [Matrix.transpose_nonsing_inv, hsymm,
    Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.2 hI.det_pos.ne'), one_mul]

end Law

end PosteriorLimit

end CausalInference
