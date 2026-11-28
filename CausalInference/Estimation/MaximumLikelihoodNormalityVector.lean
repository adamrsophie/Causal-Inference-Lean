/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.Estimation.FisherInformationVector
public import CausalInference.Estimation.VectorZEstimator
public import CausalInference.Estimation.MaximumLikelihoodNormality

/-!
# Asymptotic normality and efficiency of the maximum likelihood estimator of a vector parameter

For a family `F : ParametricFamily (Fin p → ℝ) S`, the maximum likelihood estimator is a
Z-estimator for the score vector `ψ z θ = s(θ; z)`, whose Jacobian matrix is the Hessian of the
log density: `J z θ i j = ∂_j ∂_i ℓ(θ; z)`. At a regular point the bread
`A = -E_θ₀[J (X) θ₀]` is the information matrix `I(θ₀)` (information equality and symmetry of
`I`), and so is the meat `E_θ₀[s sᵀ]` (definition of `I`). The sandwich `A⁻¹ B A⁻ᵀ` collapses to
`I(θ₀)⁻¹`, and `√n (θ̂_n - θ₀)` converges in distribution to `N(0, I(θ₀)⁻¹)` when `I(θ₀)` is
positive definite. The limit is stated in `EuclideanSpace ℝ (Fin p)`.

## Main definitions

* `CausalInference.ParametricFamily.IsScoreRegularVec`: smoothness of the log density and of the
  score on a closed ball around `θ₀`, with an integrable envelope of the Hessian entries.
* `CausalInference.ParametricFamily.IsAsymptoticallyEfficient` and `IsAsymptoticallyEfficientVec`:
  asymptotic normality with variance the inverse information, in a regular family with positive
  (positive definite) information.

## Main results

* `CausalInference.ParametricFamily.fisherInfoMatrix_transpose`: `I(θ)` is symmetric.
* `CausalInference.ParametricFamily.hasFDerivAt_logLik_of_contDiffOn`: the calculus of the
  score when the density is `C²` and positive on an open ball.
* `CausalInference.ParametricFamily.IsRegularAtVec.exists_isScoreRegularVec`: a regular point
  with an integrable envelope of the Hessian entries and measurability is score regular.
* `CausalInference.ParametricFamily.breadMatrix_scoreVec_eq_fisherInfoMatrix`,
  `meatMatrix_scoreVec_eq_fisherInfoMatrix`, `sandwich_scoreVec_eq_inv_fisherInfoMatrix`.
* `CausalInference.ParametricFamily.mle_isAsymptoticallyLinear_vec`: every coordinate of a
  consistent root of the score equations is asymptotically linear with influence function
  `(I(θ₀)⁻¹ s(θ₀; ·))_j`.
* `CausalInference.ParametricFamily.mle_tendstoInDistribution_vec`: **asymptotic normality**,
  and `mle_tendstoInDistribution_vec_of_isLocalMax` for a local maximizer of the
  log-likelihood.
* `CausalInference.ParametricFamily.mle_isAsymptoticallyEfficient` and
  `mle_isAsymptoticallyEfficientVec`: the maximum likelihood estimator is efficient.

References: A. W. van der Vaart (1998), *Asymptotic Statistics*, chapter 5; E. L. Lehmann and
G. Casella (1998), *Theory of Point Estimation*, 2nd edition, chapter 6.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Finset Metric Matrix
open scoped Topology ENNReal NNReal

namespace CausalInference

namespace ParametricFamily

variable {S : Type*} [MeasurableSpace S] {p : ℕ} {F : ParametricFamily (Fin p → ℝ) S}

/-- **The Fisher information matrix is symmetric.** -/
theorem fisherInfoMatrix_transpose (θ : Fin p → ℝ) :
    (F.fisherInfoMatrix θ)ᵀ = F.fisherInfoMatrix θ := by
  ext j k
  simp only [transpose_apply, fisherInfoMatrix, of_apply, mul_comm]

/-- The gradient `v ↦ ∑ⱼ gⱼ vⱼ` of a vector `g`, as a continuous linear form on `ℝ^p`. -/
noncomputable def gradCLM (g : Fin p → ℝ) : (Fin p → ℝ) →L[ℝ] ℝ :=
  ∑ j, g j • ContinuousLinearMap.proj j

/-- `gradCLM g v = g ⬝ᵥ v`. -/
@[simp]
theorem gradCLM_apply (g v : Fin p → ℝ) : gradCLM g v = g ⬝ᵥ v := by
  simp [gradCLM, dotProduct]

/-- The continuous linear map `v ↦ M v` of a square matrix on `ℝ^p` (sup norm). -/
noncomputable def mulVecCLM (M : Matrix (Fin p) (Fin p) ℝ) : (Fin p → ℝ) →L[ℝ] (Fin p → ℝ) :=
  LinearMap.toContinuousLinearMap (Matrix.toLin' M)

/-- `mulVecCLM M v = M *ᵥ v`. -/
@[simp]
theorem mulVecCLM_apply (M : Matrix (Fin p) (Fin p) ℝ) (v : Fin p → ℝ) :
    mulVecCLM M v = M *ᵥ v := rfl

/-- The Jacobian matrix of the score vector: `scoreJacobian θ z i j = ∂_j ∂_i ℓ(θ; z)`. -/
noncomputable def scoreJacobian (F : ParametricFamily (Fin p → ℝ) S) (θ : Fin p → ℝ) (z : S) :
    Matrix (Fin p) (Fin p) ℝ :=
  Matrix.of fun i j ↦ F.hessianLogLik j i θ z

/-- Smoothness of the score on the closed ball of radius `r > 0` around `θ₀`: the score at `θ₀`
and every Hessian entry `∂_j ∂_k ℓ(θ; ·)` on the ball are measurable; for `P_θ₀`-almost every
`z`, at every point of the ball the log density has gradient `s(θ; z)` and the score has
Jacobian matrix `scoreJacobian θ z`, the Hessian entries are continuous on the ball, and they are
bounded there by a `P_θ₀`-integrable envelope `H`. -/
structure IsScoreRegularVec (F : ParametricFamily (Fin p → ℝ) S) (θ₀ : Fin p → ℝ) (r : ℝ) :
    Prop where
  /-- The radius is positive. -/
  pos : 0 < r
  /-- The score at `θ₀` is measurable. -/
  measurable_scoreVec : Measurable (F.scoreVec θ₀)
  /-- The Hessian entries on the ball are measurable. -/
  measurable_hessianLogLik : ∀ θ ∈ closedBall θ₀ r, ∀ j k, Measurable (F.hessianLogLik j k θ)
  /-- The log density has gradient the score on the ball. -/
  hasFDerivAt_logLik : ∀ᵐ z ∂F.law θ₀, ∀ θ ∈ closedBall θ₀ r,
    HasFDerivAt (fun u ↦ F.logLik u z) (gradCLM (F.scoreVec θ z)) θ
  /-- The score has Jacobian matrix `scoreJacobian` on the ball. -/
  hasFDerivAt_scoreVec : ∀ᵐ z ∂F.law θ₀, ∀ θ ∈ closedBall θ₀ r,
    HasFDerivAt (fun u ↦ F.scoreVec u z) (mulVecCLM (F.scoreJacobian θ z)) θ
  /-- The Hessian entries are continuous on the ball. -/
  continuousOn_hessianLogLik : ∀ᵐ z ∂F.law θ₀, ∀ j k,
    ContinuousOn (fun u ↦ F.hessianLogLik j k u z) (closedBall θ₀ r)
  /-- An integrable envelope of the Hessian entries on the ball. -/
  dominated : ∃ H : S → ℝ, Integrable H (F.law θ₀) ∧
    ∀ᵐ z ∂F.law θ₀, ∀ θ ∈ closedBall θ₀ r, ∀ j k, |F.hessianLogLik j k θ z| ≤ H z

/-! ### The calculus of the score -/

/-- A continuous linear form on `ℝ^p` is the gradient of its values at the basis vectors. -/
theorem eq_gradCLM (A : (Fin p → ℝ) →L[ℝ] ℝ) : A = gradCLM fun k ↦ A (Pi.single k 1) := by
  refine ContinuousLinearMap.coe_injective (LinearMap.pi_ext fun k x ↦ ?_)
  have hx : (Pi.single k x : Fin p → ℝ) = x • Pi.single k 1 := by
    rw [← Pi.single_smul, smul_eq_mul, mul_one]
  simp only [ContinuousLinearMap.coe_coe, gradCLM_apply, dotProduct_single]
  rw [hx, map_smul, smul_eq_mul, mul_comm]

/-- **The calculus of the score.** If `η ↦ f(z; η)` is `C²` and positive on the open ball
`B = ball θ₀ ε`, then on `B`, with `L = log f(z; ·)` and `G = DL`: `L` has derivative `G`, `G`
has derivative `DG`, which is continuous on `B`; the score is `s(u; z)_k = G u e_k`, and the
Hessian entries are `∂_j ∂_k ℓ(u; z) = DG u e_j e_k`. -/
theorem logLik_calculus {θ₀ : Fin p → ℝ} {ε : ℝ} {z : S}
    (hC : ContDiffOn ℝ 2 (fun η ↦ F.density η z) (ball θ₀ ε))
    (hpos : ∀ η ∈ ball θ₀ ε, 0 < F.density η z) :
    ContinuousOn (fderiv ℝ (fderiv ℝ fun u ↦ F.logLik u z)) (ball θ₀ ε) ∧
      (∀ u ∈ ball θ₀ ε, HasFDerivAt (fun v ↦ F.logLik v z)
        (fderiv ℝ (fun v ↦ F.logLik v z) u) u) ∧
      (∀ u ∈ ball θ₀ ε, HasFDerivAt (fderiv ℝ fun v ↦ F.logLik v z)
        (fderiv ℝ (fderiv ℝ fun v ↦ F.logLik v z) u) u) ∧
      (∀ u ∈ ball θ₀ ε, ∀ k,
        F.scoreVec u z k = fderiv ℝ (fun v ↦ F.logLik v z) u (Pi.single k 1)) ∧
      ∀ u ∈ ball θ₀ ε, ∀ j k, F.hessianLogLik j k u z =
        fderiv ℝ (fderiv ℝ fun v ↦ F.logLik v z) u (Pi.single j 1) (Pi.single k 1) := by
  set B := ball θ₀ ε
  have hB : IsOpen B := isOpen_ball
  set L : (Fin p → ℝ) → ℝ := fun u ↦ F.logLik u z with hLdef
  have hL : ContDiffOn ℝ 2 L B := hC.log fun u hu ↦ (hpos u hu).ne'
  have hG : ContDiffOn ℝ 1 (fderiv ℝ L) B := hL.fderiv_of_isOpen hB (by norm_num)
  have hGG : ContDiffOn ℝ 0 (fderiv ℝ (fderiv ℝ L)) B := hG.fderiv_of_isOpen hB (by norm_num)
  have hLd : ∀ u ∈ B, HasFDerivAt L (fderiv ℝ L u) u := fun u hu ↦
    ((hL.differentiableOn (by norm_num) u hu).differentiableAt (hB.mem_nhds hu)).hasFDerivAt
  have hGd : ∀ u ∈ B, HasFDerivAt (fderiv ℝ L) (fderiv ℝ (fderiv ℝ L) u) u := fun u hu ↦
    ((hG.differentiableOn (by norm_num) u hu).differentiableAt (hB.mem_nhds hu)).hasFDerivAt
  have hslice : ∀ u ∈ B, ∀ k, HasDerivAt (fun s ↦ L (Function.update u k s))
      (fderiv ℝ L u (Pi.single k 1)) (u k) := fun u hu k ↦
    (hLd u hu).comp_hasDerivAt_of_eq (u k) (hasDerivAt_update u k (u k))
      (Function.update_eq_self k u).symm
  refine ⟨hGG.continuousOn, hLd, hGd, fun u hu k ↦ ?_, fun u hu j k ↦ ?_⟩
  · have hgd : HasFDerivAt (fun η ↦ F.density η z) (fderiv ℝ (fun η ↦ F.density η z) u) u :=
      ((hC.differentiableOn (by norm_num) u hu).differentiableAt (hB.mem_nhds hu)).hasFDerivAt
    have hGu : fderiv ℝ L u = (F.density u z)⁻¹ • fderiv ℝ (fun η ↦ F.density η z) u :=
      (hgd.log (hpos u hu).ne').fderiv
    have hd : HasDerivAt (fun t ↦ F.density (Function.update u k t) z)
        (fderiv ℝ (fun η ↦ F.density η z) u (Pi.single k 1)) (u k) :=
      hgd.comp_hasDerivAt_of_eq (u k) (hasDerivAt_update u k (u k))
        (Function.update_eq_self k u).symm
    rw [scoreVec, partialDeriv, hd.deriv, hGu]
    simp [div_eq_inv_mul]
  · have hev : ∀ᶠ t in 𝓝 (u j), Function.update u j t ∈ B :=
      (tendsto_update u j) (hB.mem_nhds hu)
    have hR : HasDerivAt (fun t ↦ fderiv ℝ L (Function.update u j t) (Pi.single k 1))
        (fderiv ℝ (fderiv ℝ L) u (Pi.single j 1) (Pi.single k 1)) (u j) := by
      have h1 := (hGd u hu).comp_hasDerivAt_of_eq (u j) (hasDerivAt_update u j (u j))
        (Function.update_eq_self j u).symm
      exact ((ContinuousLinearMap.apply ℝ ℝ (Pi.single k (1 : ℝ))).hasFDerivAt).comp_hasDerivAt
        (u j) h1
    refine (hR.congr_of_eventuallyEq ?_).deriv
    filter_upwards [hev] with t ht
    exact (hslice _ ht k).deriv

/-- On an open ball where the density is `C²` and positive, the Hessian entries of the log
density are continuous. -/
theorem continuousOn_hessianLogLik_of_contDiffOn {θ₀ : Fin p → ℝ} {ε : ℝ} {z : S}
    (hC : ContDiffOn ℝ 2 (fun η ↦ F.density η z) (ball θ₀ ε))
    (hpos : ∀ η ∈ ball θ₀ ε, 0 < F.density η z) (j k : Fin p) :
    ContinuousOn (fun u ↦ F.hessianLogLik j k u z) (ball θ₀ ε) := by
  obtain ⟨hc, -, -, -, hh⟩ := logLik_calculus hC hpos
  exact ((hc.clm_apply continuousOn_const).clm_apply continuousOn_const).congr
    fun u hu ↦ hh u hu j k

/-- On an open ball where the density is `C²` and positive, the log density has gradient the
score and the score has Jacobian matrix `scoreJacobian`. -/
theorem hasFDerivAt_logLik_of_contDiffOn {θ₀ : Fin p → ℝ} {ε : ℝ} {z : S}
    (hC : ContDiffOn ℝ 2 (fun η ↦ F.density η z) (ball θ₀ ε))
    (hpos : ∀ η ∈ ball θ₀ ε, 0 < F.density η z) {u : Fin p → ℝ} (hu : u ∈ ball θ₀ ε) :
    HasFDerivAt (fun v ↦ F.logLik v z) (gradCLM (F.scoreVec u z)) u ∧
      HasFDerivAt (fun v ↦ F.scoreVec v z) (mulVecCLM (F.scoreJacobian u z)) u := by
  obtain ⟨-, hLd, hGd, hs, hh⟩ := logLik_calculus hC hpos
  set G := fderiv ℝ fun v ↦ F.logLik v z
  have hsu : F.scoreVec u z = fun k ↦ G u (Pi.single k 1) := funext (hs u hu)
  refine ⟨?_, ?_⟩
  · rw [hsu, ← eq_gradCLM]
    exact hLd u hu
  · have hev : (fun v ↦ F.scoreVec v z) =ᶠ[𝓝 u] fun v k ↦ G v (Pi.single k 1) := by
      filter_upwards [isOpen_ball.mem_nhds hu] with v hv
      exact funext (hs v hv)
    refine HasFDerivAt.congr_of_eventuallyEq (hasFDerivAt_pi'' fun k ↦ ?_) hev
    have h1 := ((ContinuousLinearMap.apply ℝ ℝ (Pi.single k (1 : ℝ))).hasFDerivAt).comp u
      (hGd u hu)
    refine h1.congr_fderiv ?_
    rw [eq_gradCLM ((ContinuousLinearMap.apply ℝ ℝ (Pi.single k (1 : ℝ))).comp
      (fderiv ℝ G u))]
    ext v
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply, mulVecCLM_apply,
      gradCLM_apply, ContinuousLinearMap.apply_apply, mulVec, scoreJacobian, dotProduct,
      of_apply, hh u hu, mul_comm]

/-- **Score regularity from smoothness.** If for `P_θ₀`-almost every `z` the density is `C²` and
positive on `ball θ₀ ε`, `0 < r < ε`, the score at `θ₀` and the Hessian entries on the closed
ball of radius `r` are measurable, and the Hessian entries have an integrable envelope there,
then the score is regular on that closed ball. -/
theorem IsScoreRegularVec.of_contDiffOn {θ₀ : Fin p → ℝ} {ε r : ℝ} (hr : 0 < r) (hrε : r < ε)
    (hC : ∀ᵐ z ∂F.law θ₀, ContDiffOn ℝ 2 (fun η ↦ F.density η z) (ball θ₀ ε))
    (hpos : ∀ᵐ z ∂F.law θ₀, ∀ η ∈ ball θ₀ ε, 0 < F.density η z)
    (hsm : Measurable (F.scoreVec θ₀))
    (hhm : ∀ θ ∈ closedBall θ₀ r, ∀ j k, Measurable (F.hessianLogLik j k θ)) {H : S → ℝ}
    (hH : Integrable H (F.law θ₀))
    (hdom : ∀ᵐ z ∂F.law θ₀, ∀ θ ∈ closedBall θ₀ r, ∀ j k, |F.hessianLogLik j k θ z| ≤ H z) :
    F.IsScoreRegularVec θ₀ r := by
  have hsub : closedBall θ₀ r ⊆ ball θ₀ ε := closedBall_subset_ball hrε
  refine ⟨hr, hsm, hhm, ?_, ?_, ?_, ⟨H, hH, hdom⟩⟩
  · filter_upwards [hC, hpos] with z h1 h2 θ hθ
    exact (hasFDerivAt_logLik_of_contDiffOn h1 h2 (hsub hθ)).1
  · filter_upwards [hC, hpos] with z h1 h2 θ hθ
    exact (hasFDerivAt_logLik_of_contDiffOn h1 h2 (hsub hθ)).2
  · filter_upwards [hC, hpos] with z h1 h2 j k
    exact (continuousOn_hessianLogLik_of_contDiffOn h1 h2 j k).mono hsub

/-- A regular point has a ball inside `Θ` on which, for `P_θ₀`-almost every `z`, the density is
`C²` and positive. -/
theorem IsRegularAtVec.exists_ball_pos {θ₀ : Fin p → ℝ} (h : F.IsRegularAtVec θ₀) :
    ∃ ε > 0, ball θ₀ ε ⊆ F.Θ ∧
      (∀ᵐ z ∂F.law θ₀, ContDiffOn ℝ 2 (fun η ↦ F.density η z) (ball θ₀ ε)) ∧
      ∀ᵐ z ∂F.law θ₀, ∀ η ∈ ball θ₀ ε, 0 < F.density η z := by
  obtain ⟨ε, hε, hball, hC, -⟩ := h.smooth_dominated
  obtain ⟨δ, hδ, hsupp⟩ := Metric.eventually_nhds_iff.1 h.support
  refine ⟨min ε δ, lt_min hε hδ, (ball_subset_ball (min_le_left _ _)).trans hball,
    (ae_law_of_ae hC).mono fun z hz ↦ hz.mono (ball_subset_ball (min_le_left _ _)), ?_⟩
  filter_upwards [ae_law_pos (F := F) (θ := θ₀)] with z hz η hη
  exact (hsupp (lt_of_lt_of_le (mem_ball.1 hη) (min_le_right _ _)) z).2 hz

/-- **A regular point is score regular.** At a regular point, if the score at `θ₀` and the
Hessian entries on a neighborhood `U` of `θ₀` are measurable and the Hessian entries have a
`P_θ₀`-integrable envelope on `U`, the score is regular on some closed ball inside `U`. -/
theorem IsRegularAtVec.exists_isScoreRegularVec {θ₀ : Fin p → ℝ} (h : F.IsRegularAtVec θ₀)
    {U : Set (Fin p → ℝ)} (hU : U ∈ 𝓝 θ₀) (hsm : Measurable (F.scoreVec θ₀))
    (hhm : ∀ θ ∈ U, ∀ j k, Measurable (F.hessianLogLik j k θ)) {H : S → ℝ}
    (hH : Integrable H (F.law θ₀))
    (hdom : ∀ᵐ z ∂F.law θ₀, ∀ θ ∈ U, ∀ j k, |F.hessianLogLik j k θ z| ≤ H z) :
    ∃ r, closedBall θ₀ r ⊆ U ∧ F.IsScoreRegularVec θ₀ r := by
  obtain ⟨ε, hε, -, hC, hpos⟩ := h.exists_ball_pos
  obtain ⟨δ, hδ, hδU⟩ := Metric.mem_nhds_iff.1 hU
  set r := min ε δ / 2
  have hr : 0 < r := half_pos (lt_min hε hδ)
  have h1 := min_le_left ε δ
  have h2 := min_le_right ε δ
  have h3 := lt_min hε hδ
  have hrU : closedBall θ₀ r ⊆ U :=
    (closedBall_subset_ball (show min ε δ / 2 < δ by linarith)).trans hδU
  exact ⟨r, hrU, IsScoreRegularVec.of_contDiffOn hr (show min ε δ / 2 < ε by linarith) hC hpos hsm
    (fun θ hθ ↦ hhm θ (hrU hθ)) hH (hdom.mono fun z hz θ hθ ↦ hz θ (hrU hθ))⟩

/-! ### The score as an estimating function in Euclidean coordinates -/

/-- The score vector as an estimating function on `ℝ^p = EuclideanSpace ℝ (Fin p)`. -/
noncomputable def scoreVecE (F : ParametricFamily (Fin p → ℝ) S) (z : S)
    (θ : EuclideanSpace ℝ (Fin p)) : EuclideanSpace ℝ (Fin p) :=
  WithLp.toLp 2 (F.scoreVec (WithLp.ofLp θ) z)

/-- The Jacobian matrix of `scoreVecE`. -/
noncomputable def scoreJacobianE (F : ParametricFamily (Fin p → ℝ) S) (z : S)
    (θ : EuclideanSpace ℝ (Fin p)) : Matrix (Fin p) (Fin p) ℝ :=
  F.scoreJacobian (WithLp.ofLp θ) z

/-- The Euclidean closed ball lies in the closed ball for the sup norm. -/
theorem ofLp_mem_closedBall {θ₀ : Fin p → ℝ} {r : ℝ} {θ : EuclideanSpace ℝ (Fin p)}
    (hθ : θ ∈ closedBall (WithLp.toLp 2 θ₀) r) : WithLp.ofLp θ ∈ closedBall θ₀ r := by
  rw [mem_closedBall] at hθ ⊢
  refine (dist_pi_le_iff (dist_nonneg.trans hθ)).2 fun i ↦ ?_
  exact (PiLp.dist_apply_le θ (WithLp.toLp 2 θ₀) i).trans hθ

/-- The derivative of the Euclidean score. -/
theorem hasFDerivAt_scoreVecE {θ : EuclideanSpace ℝ (Fin p)} {z : S}
    (h : HasFDerivAt (fun u ↦ F.scoreVec u z) (mulVecCLM (F.scoreJacobian (WithLp.ofLp θ) z))
      (WithLp.ofLp θ)) :
    HasFDerivAt (F.scoreVecE z) (Matrix.toEuclideanCLM (𝕜 := ℝ) (F.scoreJacobianE z θ)) θ := by
  set e := PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin p ↦ ℝ)
  have hc := (e.symm : (Fin p → ℝ) →L[ℝ] EuclideanSpace ℝ (Fin p)).hasFDerivAt.comp θ
    ((show HasFDerivAt (fun u ↦ F.scoreVec u z) _ (e θ) from h).comp θ e.hasFDerivAt)
  refine hc.congr_fderiv ?_
  ext v i
  rw [← matrixCLM_eq_toEuclideanCLM, matrixCLM_apply_apply]
  rfl

variable {θ₀ : Fin p → ℝ}

/-- **The bread of the score equation is the information.** At a regular point, the bread
`-E_θ₀[J]` of the score with Jacobian `scoreJacobianE` is `I(θ₀)`: the information equality
gives `-E_θ₀[∂_j ∂_i ℓ] = I(θ₀)_{ji}`, and `I(θ₀)` is symmetric. -/
theorem breadMatrix_scoreVec_eq_fisherInfoMatrix (hreg : F.IsRegularAtVec θ₀) :
    breadMatrix (F.law θ₀) F.scoreJacobianE (WithLp.toLp 2 θ₀) = F.fisherInfoMatrix θ₀ := by
  ext i j
  change -∫ z, F.hessianLogLik j i θ₀ z ∂F.law θ₀ = _
  rw [← (hreg.information_equality j i).2.2]
  simp only [fisherInfoMatrix, of_apply, mul_comm]

/-- **The meat of the score equation is the information**, by definition of `I(θ₀)`. -/
theorem meatMatrix_scoreVec_eq_fisherInfoMatrix :
    meatMatrix (F.law θ₀) F.scoreVecE (WithLp.toLp 2 θ₀) = F.fisherInfoMatrix θ₀ := rfl

/-- **The sandwich collapses to the inverse information.** At a regular point with positive
definite information, `A⁻¹ B A⁻ᵀ = I(θ₀)⁻¹` for the bread `A` and meat `B` of the score. -/
theorem sandwich_scoreVec_eq_inv_fisherInfoMatrix (hreg : F.IsRegularAtVec θ₀)
    (hI : (F.fisherInfoMatrix θ₀).PosDef) :
    (breadMatrix (F.law θ₀) F.scoreJacobianE (WithLp.toLp 2 θ₀))⁻¹ *
        meatMatrix (F.law θ₀) F.scoreVecE (WithLp.toLp 2 θ₀) *
        ((breadMatrix (F.law θ₀) F.scoreJacobianE (WithLp.toLp 2 θ₀))⁻¹)ᵀ =
      (F.fisherInfoMatrix θ₀)⁻¹ := by
  rw [breadMatrix_scoreVec_eq_fisherInfoMatrix hreg, meatMatrix_scoreVec_eq_fisherInfoMatrix,
    transpose_nonsing_inv, fisherInfoMatrix_transpose,
    nonsing_inv_mul _ (isUnit_iff_ne_zero.2 hI.det_pos.ne'), Matrix.one_mul]

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {O : ℕ → Ω → S}

/-- The hypotheses of the vector Z-estimator theorems for the score in Euclidean coordinates, at
a regular point whose score is regular on a closed ball, for an i.i.d. sample with law
`P_θ₀`. -/
theorem zEstimator_hypotheses_scoreVecE [IsProbabilityMeasure μ] (hO : IsIIDSample O μ)
    (hlaw : μ.map (O 0) = F.law θ₀) (hreg : F.IsRegularAtVec θ₀) {r : ℝ}
    (hs : F.IsScoreRegularVec θ₀ r) :
    (Measurable fun z ↦ F.scoreVecE z (WithLp.toLp 2 θ₀)) ∧
    (∀ θ ∈ closedBall (WithLp.toLp 2 θ₀) r, ∀ i j,
      Measurable fun z ↦ F.scoreJacobianE z θ i j) ∧
    (∀ᵐ z ∂(μ.map (O 0)), ∀ θ ∈ closedBall (WithLp.toLp 2 θ₀) r,
      HasFDerivAt (F.scoreVecE z) (Matrix.toEuclideanCLM (𝕜 := ℝ) (F.scoreJacobianE z θ)) θ) ∧
    (∀ᵐ z ∂(μ.map (O 0)), ∀ i j,
      ContinuousOn (fun θ ↦ F.scoreJacobianE z θ i j) (closedBall (WithLp.toLp 2 θ₀) r)) ∧
    (∃ H : S → ℝ, Integrable H (μ.map (O 0)) ∧ ∀ᵐ z ∂(μ.map (O 0)),
      ∀ θ ∈ closedBall (WithLp.toLp 2 θ₀) r, ∀ i j, |F.scoreJacobianE z θ i j| ≤ H z) ∧
    μ[fun ω ↦ F.scoreVecE (O 0 ω) (WithLp.toLp 2 θ₀)] = 0 ∧
    MemLp (fun ω ↦ F.scoreVecE (O 0 ω) (WithLp.toLp 2 θ₀)) 2 μ := by
  have hθ₀ : θ₀ ∈ F.Θ := mem_of_mem_nhds hreg.mem_nhds
  have := isProbabilityMeasure_law hθ₀
  have hX := hO.aemeasurable 0
  obtain ⟨H, hH, hdom⟩ := hs.dominated
  have hcomp : ∀ k, Measurable fun x ↦ F.scoreVec θ₀ x k := fun k ↦
    (measurable_pi_apply k).comp hs.measurable_scoreVec
  have hψm : Measurable fun z ↦ F.scoreVecE z (WithLp.toLp 2 θ₀) :=
    (PiLp.continuous_toLp 2 _).measurable.comp hs.measurable_scoreVec
  have hmk : ∀ k, MemLp (fun ω ↦ F.scoreVec θ₀ (O 0 ω) k) 2 μ := fun k ↦
    (memLp_map_measure_iff (hcomp k).aestronglyMeasurable hX).1
      (by rw [hlaw]; exact hreg.memLp_scoreVec k)
  have hB : MemLp (fun ω ↦ F.scoreVecE (O 0 ω) (WithLp.toLp 2 θ₀)) 2 μ :=
    memLp_piLp_iff.2 hmk
  refine ⟨hψm, fun θ hθ i j ↦ hs.measurable_hessianLogLik _ (ofLp_mem_closedBall hθ) j i,
    ?_, ?_, ⟨H, by rw [hlaw]; exact hH, ?_⟩, ?_, hB⟩
  · rw [hlaw]
    filter_upwards [hs.hasFDerivAt_scoreVec] with z hz θ hθ
    exact hasFDerivAt_scoreVecE (hz _ (ofLp_mem_closedBall hθ))
  · rw [hlaw]
    filter_upwards [hs.continuousOn_hessianLogLik] with z hz i j
    exact (hz j i).comp (PiLp.continuous_ofLp 2 _).continuousOn fun θ hθ ↦ ofLp_mem_closedBall hθ
  · rw [hlaw]
    filter_upwards [hdom] with z hz θ hθ i j
    exact hz _ (ofLp_mem_closedBall hθ) j i
  · ext k
    rw [eval_integral_piLp (fun j ↦ (hB.integrable one_le_two).eval_piLp j)]
    change ∫ ω, F.scoreVec θ₀ (O 0 ω) k ∂μ = 0
    rw [← integral_map hX (hcomp k).aestronglyMeasurable, hlaw,
      integral_scoreVec_eq_zero hreg.mem_nhds hreg.interchange.1.self_of_nhds k]

/-- An exact root of the score equations with probability tending to one makes the normalized
estimating equation tend to zero in probability. -/
theorem tendstoInMeasure_sqrt_smul_scoreVecE {θh : ℕ → Ω → Fin p → ℝ}
    (hroot : WithProbTendingToOne μ
      (fun n ↦ {ω | ∑ i ∈ range n, F.scoreVec (θh n ω) (O i ω) = 0})) :
    TendstoInMeasure μ (fun (n : ℕ) ω ↦ √(n : ℝ) • ((n : ℝ)⁻¹ •
      ∑ i ∈ range n, F.scoreVecE (O i ω) (WithLp.toLp 2 (θh n ω)))) atTop (fun _ ↦ 0) := by
  refine (tendstoInMeasure_const (μ := μ) (0 : EuclideanSpace ℝ (Fin p))).congr_withProbTendingToOne
    hroot fun n ω hω ↦ ?_
  simp only [Set.mem_ofPred_eq] at hω
  have : ∑ i ∈ range n, F.scoreVecE (O i ω) (WithLp.toLp 2 (θh n ω)) = 0 := by
    change ∑ i ∈ range n, WithLp.toLp 2 (F.scoreVec (θh n ω) (O i ω)) = 0
    rw [← WithLp.toLp_sum, hω]
    rfl
  simp [this]

/-- **Asymptotic normality of the maximum likelihood estimator, vector parameter.** Let `O` be
an i.i.d. sample with law `P_θ₀`, `θ₀` a regular point (`IsRegularAtVec`) with positive definite
information, the score regular on a closed ball around `θ₀` (`IsScoreRegularVec`), `θh`
consistent for `θ₀` and almost everywhere measurable, and `θh n` a root of the score equations
with probability tending to one. Then `√n (θh n - θ₀)` converges in distribution to every random
vector with law `N(0, I(θ₀)⁻¹)`. -/
theorem mle_tendstoInDistribution_vec [IsProbabilityMeasure μ] (hO : IsIIDSample O μ)
    (hlaw : μ.map (O 0) = F.law θ₀) (hreg : F.IsRegularAtVec θ₀) {r : ℝ}
    (hs : F.IsScoreRegularVec θ₀ r) (hI : (F.fisherInfoMatrix θ₀).PosDef)
    {θh : ℕ → Ω → Fin p → ℝ} (hθm : ∀ n, AEMeasurable (θh n) μ)
    (hθ : TendstoInMeasure μ θh atTop (fun _ ↦ θ₀))
    (hroot : WithProbTendingToOne μ
      (fun n ↦ {ω | ∑ i ∈ range n, F.scoreVec (θh n ω) (O i ω) = 0}))
    {Ω' : Type*} {mΩ' : MeasurableSpace Ω'} {P' : Measure Ω'} [IsProbabilityMeasure P']
    {Y : Ω' → EuclideanSpace ℝ (Fin p)}
    (hY : HasLaw Y (multivariateGaussian 0 (F.fisherInfoMatrix θ₀)⁻¹) P') :
    TendstoInDistribution (fun (n : ℕ) ω ↦
      √(n : ℝ) • (WithLp.toLp 2 (θh n ω) - WithLp.toLp 2 θ₀ : EuclideanSpace ℝ (Fin p))) atTop Y
      (fun _ ↦ μ) P' := by
  obtain ⟨hψm, hJm, hderiv, hcont, ⟨H, hH, hdom⟩, hzero, hB⟩ :=
    zEstimator_hypotheses_scoreVecE hO hlaw hreg hs
  have hA : (breadMatrix (μ.map (O 0)) F.scoreJacobianE (WithLp.toLp 2 θ₀)).det ≠ 0 := by
    rw [hlaw, breadMatrix_scoreVec_eq_fisherInfoMatrix hreg]; exact hI.det_pos.ne'
  refine vectorZEstimator_tendstoInDistribution hO hs.pos hψm hJm hderiv hcont hH hdom hzero hB
    hA (θh := fun n ω ↦ WithLp.toLp 2 (θh n ω))
    (fun n ↦ (PiLp.continuous_toLp 2 _).measurable.comp_aemeasurable (hθm n))
    (hθ.comp_continuousAt (PiLp.continuous_toLp 2 _).continuousAt)
    (tendstoInMeasure_sqrt_smul_scoreVecE hroot) ?_
  rw [hlaw, sandwich_scoreVec_eq_inv_fisherInfoMatrix hreg hI]
  exact hY

/-- **Asymptotic linearity of the maximum likelihood estimator, vector parameter.** Under the
hypotheses of `mle_tendstoInDistribution_vec` (measurability of `θh n` is not needed), every
coordinate `θh n j` is asymptotically linear at `θ₀ j` with influence function
`z ↦ (I(θ₀)⁻¹ s(θ₀; z))_j`. -/
theorem mle_isAsymptoticallyLinear_vec [IsProbabilityMeasure μ] (hO : IsIIDSample O μ)
    (hlaw : μ.map (O 0) = F.law θ₀) (hreg : F.IsRegularAtVec θ₀) {r : ℝ}
    (hs : F.IsScoreRegularVec θ₀ r) (hI : (F.fisherInfoMatrix θ₀).PosDef)
    {θh : ℕ → Ω → Fin p → ℝ} (hθ : TendstoInMeasure μ θh atTop (fun _ ↦ θ₀))
    (hroot : WithProbTendingToOne μ
      (fun n ↦ {ω | ∑ i ∈ range n, F.scoreVec (θh n ω) (O i ω) = 0})) (j : Fin p) :
    IsAsymptoticallyLinear (fun n ω ↦ θh n ω j) (θ₀ j)
      (fun z ↦ ((F.fisherInfoMatrix θ₀)⁻¹ *ᵥ F.scoreVec θ₀ z) j) O μ := by
  obtain ⟨hψm, hJm, hderiv, hcont, ⟨H, hH, hdom⟩, hzero, hB⟩ :=
    zEstimator_hypotheses_scoreVecE hO hlaw hreg hs
  have hbread : breadMatrix (μ.map (O 0)) F.scoreJacobianE (WithLp.toLp 2 θ₀) =
      F.fisherInfoMatrix θ₀ := by rw [hlaw, breadMatrix_scoreVec_eq_fisherInfoMatrix hreg]
  have hA : (breadMatrix (μ.map (O 0)) F.scoreJacobianE (WithLp.toLp 2 θ₀)).det ≠ 0 := by
    rw [hbread]; exact hI.det_pos.ne'
  have h := vectorZEstimator_isAsymptoticallyLinear hO hs.pos hψm hJm hderiv hcont hH hdom hzero
    hB hA (θh := fun n ω ↦ WithLp.toLp 2 (θh n ω))
    (hθ.comp_continuousAt (PiLp.continuous_toLp 2 _).continuousAt)
    (tendstoInMeasure_sqrt_smul_scoreVecE hroot) j
  rw [hbread] at h
  exact h

/-- **A local maximizer of the log-likelihood solves the score equations.** If the log density
has gradient the score on the closed ball (`IsScoreRegularVec`), `θh` is consistent and `θh n`
is a local maximizer of `θ ↦ ∑_{i < n} ℓ(θ; O_i)` with probability tending to one, then `θh n`
is a root of the score equations with probability tending to one. -/
theorem withProbTendingToOne_scoreVec_eq_zero_of_isLocalMax (hO : IsIIDSample O μ)
    (hlaw : μ.map (O 0) = F.law θ₀) {r : ℝ} (hs : F.IsScoreRegularVec θ₀ r)
    {θh : ℕ → Ω → Fin p → ℝ} (hθ : TendstoInMeasure μ θh atTop (fun _ ↦ θ₀))
    (hmax : WithProbTendingToOne μ
      (fun n ↦ {ω | IsLocalMax (fun θ ↦ ∑ i ∈ range n, F.logLik θ (O i ω)) (θh n ω)})) :
    WithProbTendingToOne μ
      (fun n ↦ {ω | ∑ i ∈ range n, F.scoreVec (θh n ω) (O i ω) = 0}) := by
  refine ((hmax.inter (hθ.withProbTendingToOne_dist_lt hs.pos)).inter
    (WithProbTendingToOne.of_ae (hO.ae_forall (hlaw ▸ hs.hasFDerivAt_logLik)))).mono
    fun n ω hω ↦ ?_
  obtain ⟨⟨h1, h2⟩, h3⟩ := hω
  simp only [Set.mem_ofPred_eq] at h1 h2 h3 ⊢
  have hin : θh n ω ∈ closedBall θ₀ r := mem_closedBall.2 h2.le
  have hd := HasFDerivAt.fun_sum (u := range n) fun i _ ↦ h3 i _ hin
  have h0 := h1.hasFDerivAt_eq_zero hd
  funext k
  have := congrArg (fun A : (Fin p → ℝ) →L[ℝ] ℝ ↦ A (Pi.single k 1)) h0
  simpa [Finset.sum_apply] using this

/-- **Asymptotic normality of a local maximizer of the log-likelihood, vector parameter.** The
form of `mle_tendstoInDistribution_vec` in which `θh n` is a local maximizer of the sample
log-likelihood with probability tending to one. -/
theorem mle_tendstoInDistribution_vec_of_isLocalMax [IsProbabilityMeasure μ]
    (hO : IsIIDSample O μ) (hlaw : μ.map (O 0) = F.law θ₀) (hreg : F.IsRegularAtVec θ₀)
    {r : ℝ} (hs : F.IsScoreRegularVec θ₀ r) (hI : (F.fisherInfoMatrix θ₀).PosDef)
    {θh : ℕ → Ω → Fin p → ℝ} (hθm : ∀ n, AEMeasurable (θh n) μ)
    (hθ : TendstoInMeasure μ θh atTop (fun _ ↦ θ₀))
    (hmax : WithProbTendingToOne μ
      (fun n ↦ {ω | IsLocalMax (fun θ ↦ ∑ i ∈ range n, F.logLik θ (O i ω)) (θh n ω)}))
    {Ω' : Type*} {mΩ' : MeasurableSpace Ω'} {P' : Measure Ω'} [IsProbabilityMeasure P']
    {Y : Ω' → EuclideanSpace ℝ (Fin p)}
    (hY : HasLaw Y (multivariateGaussian 0 (F.fisherInfoMatrix θ₀)⁻¹) P') :
    TendstoInDistribution (fun (n : ℕ) ω ↦
      √(n : ℝ) • (WithLp.toLp 2 (θh n ω) - WithLp.toLp 2 θ₀ : EuclideanSpace ℝ (Fin p))) atTop Y
      (fun _ ↦ μ) P' :=
  mle_tendstoInDistribution_vec hO hlaw hreg hs hI hθm hθ
    (withProbTendingToOne_scoreVec_eq_zero_of_isLocalMax hO hlaw hs hθ hmax) hY

/-! ### Asymptotic efficiency -/

/-- **Asymptotic efficiency of an estimator sequence, real parameter.** In a family regular at
`θ₀` with positive information, `√n (θh n - θ₀)` converges in distribution to `N(0, I(θ₀)⁻¹)`:
the limit variance is the Cramér-Rao bound. The limit is stated for the identity under the
Gaussian law; `IsAsymptoticallyEfficient.tendstoInDistribution` gives every other variable with
that law. -/
def IsAsymptoticallyEfficient (F : ParametricFamily ℝ S) (θh : ℕ → Ω → ℝ) (θ₀ : ℝ)
    (μ : Measure Ω) [IsProbabilityMeasure μ] : Prop :=
  F.IsRegularAt θ₀ ∧ 0 < F.fisherInfo θ₀ ∧
    TendstoInDistribution (fun (n : ℕ) ω ↦ √(n : ℝ) * (θh n ω - θ₀)) atTop id (fun _ ↦ μ)
      (gaussianReal 0 (F.fisherInfo θ₀)⁻¹.toNNReal)

/-- **Asymptotic efficiency of an estimator sequence, vector parameter.** In a family regular at
`θ₀` with positive definite information matrix, `√n (θh n - θ₀)` converges in distribution to
`N(0, I(θ₀)⁻¹)` in `ℝ^p`. -/
def IsAsymptoticallyEfficientVec (F : ParametricFamily (Fin p → ℝ) S) (θh : ℕ → Ω → Fin p → ℝ)
    (θ₀ : Fin p → ℝ) (μ : Measure Ω) [IsProbabilityMeasure μ] : Prop :=
  F.IsRegularAtVec θ₀ ∧ (F.fisherInfoMatrix θ₀).PosDef ∧
    TendstoInDistribution (fun (n : ℕ) ω ↦
      √(n : ℝ) • (WithLp.toLp 2 (θh n ω) - WithLp.toLp 2 θ₀ : EuclideanSpace ℝ (Fin p))) atTop
      id (fun _ ↦ μ) (multivariateGaussian 0 (F.fisherInfoMatrix θ₀)⁻¹)

/-- An asymptotically efficient estimator converges to every variable with law
`N(0, I(θ₀)⁻¹)`. -/
theorem IsAsymptoticallyEfficient.tendstoInDistribution [IsProbabilityMeasure μ]
    {G : ParametricFamily ℝ S}
    {θh : ℕ → Ω → ℝ} {t₀ : ℝ} (h : G.IsAsymptoticallyEfficient θh t₀ μ)
    {Ω' : Type*} {mΩ' : MeasurableSpace Ω'} {P' : Measure Ω'} [IsProbabilityMeasure P']
    {Y : Ω' → ℝ} (hY : HasLaw Y (gaussianReal 0 (G.fisherInfo t₀)⁻¹.toNNReal) P') :
    TendstoInDistribution (fun (n : ℕ) ω ↦ √(n : ℝ) * (θh n ω - t₀)) atTop Y (fun _ ↦ μ) P' :=
  h.2.2.of_hasLaw HasLaw.id hY

/-- An asymptotically efficient estimator of a vector parameter converges to every random
vector with law `N(0, I(θ₀)⁻¹)`. -/
theorem IsAsymptoticallyEfficientVec.tendstoInDistribution [IsProbabilityMeasure μ]
    {θh : ℕ → Ω → Fin p → ℝ}
    (h : F.IsAsymptoticallyEfficientVec θh θ₀ μ)
    {Ω' : Type*} {mΩ' : MeasurableSpace Ω'} {P' : Measure Ω'} [IsProbabilityMeasure P']
    {Y : Ω' → EuclideanSpace ℝ (Fin p)}
    (hY : HasLaw Y (multivariateGaussian 0 (F.fisherInfoMatrix θ₀)⁻¹) P') :
    TendstoInDistribution (fun (n : ℕ) ω ↦
      √(n : ℝ) • (WithLp.toLp 2 (θh n ω) - WithLp.toLp 2 θ₀ : EuclideanSpace ℝ (Fin p))) atTop Y
      (fun _ ↦ μ) P' :=
  h.2.2.of_hasLaw HasLaw.id hY

/-- **The maximum likelihood estimator is asymptotically efficient, real parameter**, under the
hypotheses of `mle_tendstoInDistribution`. -/
theorem mle_isAsymptoticallyEfficient [IsProbabilityMeasure μ] {G : ParametricFamily ℝ S}
    {t₀ : ℝ} (hO : IsIIDSample O μ) (hlaw : μ.map (O 0) = G.law t₀) (hreg : G.IsRegularAt t₀)
    {r : ℝ} (hs : G.IsScoreRegular t₀ r) (hI : 0 < G.fisherInfo t₀) {θh : ℕ → Ω → ℝ}
    (hθm : ∀ n, AEMeasurable (θh n) μ) (hθ : IsConsistent θh t₀ μ)
    (hroot : WithProbTendingToOne μ
      (fun n ↦ {ω | ∑ i ∈ range n, G.score (θh n ω) (O i ω) = 0})) :
    G.IsAsymptoticallyEfficient θh t₀ μ :=
  ⟨hreg, hI, mle_tendstoInDistribution hO hlaw hreg hs hI hθm hθ hroot HasLaw.id⟩

/-- **The maximum likelihood estimator is asymptotically efficient, vector parameter**, under
the hypotheses of `mle_tendstoInDistribution_vec`. -/
theorem mle_isAsymptoticallyEfficientVec [IsProbabilityMeasure μ] (hO : IsIIDSample O μ)
    (hlaw : μ.map (O 0) = F.law θ₀) (hreg : F.IsRegularAtVec θ₀) {r : ℝ}
    (hs : F.IsScoreRegularVec θ₀ r) (hI : (F.fisherInfoMatrix θ₀).PosDef)
    {θh : ℕ → Ω → Fin p → ℝ} (hθm : ∀ n, AEMeasurable (θh n) μ)
    (hθ : TendstoInMeasure μ θh atTop (fun _ ↦ θ₀))
    (hroot : WithProbTendingToOne μ
      (fun n ↦ {ω | ∑ i ∈ range n, F.scoreVec (θh n ω) (O i ω) = 0})) :
    F.IsAsymptoticallyEfficientVec θh θ₀ μ :=
  ⟨hreg, hI, mle_tendstoInDistribution_vec hO hlaw hreg hs hI hθm hθ hroot HasLaw.id⟩

end ParametricFamily

end CausalInference
