/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.Estimation.MaximumLikelihoodNormalityVector

/-!
# One dimensional submodels of a vector family

For a family `F : ParametricFamily (Fin p → ℝ) S`, a point `θ₀` and a direction `u ∈ ℝ^p`, the
line `t ↦ P_{θ₀ + t u}` is a scalar family. At `t = 0` its score is `uᵀ s(θ₀; ·)` and its
information is `uᵀ I(θ₀) u`. The scalar regularity conditions of the line follow from those of
the vector family, so that every scalar theorem (local asymptotic normality, the Hájek bound, the
characterization of regular asymptotically linear estimators) applies along every line.

## Main definitions

* `CausalInference.ParametricFamily.line F θ₀ u`: the scalar family `t ↦ f(·; θ₀ + t u)` with
  parameter set `{t | θ₀ + t u ∈ Θ}`.

## Main results

* `CausalInference.ParametricFamily.pi_line_law`: the sample family of the line at `t` is the
  sample family of `F` at `θ₀ + t u`.
* `CausalInference.ParametricFamily.line_score_zero_ae`: the score of the line at `0` is
  `uᵀ s(θ₀; ·)` almost surely.
* `CausalInference.ParametricFamily.line_fisherInfo`: the information of the line at `0` is
  `uᵀ I(θ₀) u`, positive when `I(θ₀)` is positive definite and `u ≠ 0`.
* `CausalInference.ParametricFamily.IsRegularAtVec.line_isRegularAt`: a regular point of `F` is a
  regular point of every line through it.
* `CausalInference.ParametricFamily.line_isScoreRegular`: at a regular point with regular score
  (`IsScoreRegularVec`), the line satisfies `IsScoreRegular 0 r'` for some `r' > 0` and
  `∂_t ℓ(θ₀ + t u; z) = s_line(t; z)` on the closed ball, given the measurability of the score of
  the line at `0` and of the second derivatives of its log density near `0`. These two
  measurability conditions concern functions defined everywhere which the hypotheses on `F`
  identify only almost everywhere; they hold on a discrete sample space
  (`line_isScoreRegular_of_discrete`).

References: A. W. van der Vaart (1998), *Asymptotic Statistics*, chapters 7 and 8; P. J. Bickel,
C. A. J. Klaassen, Y. Ritov and J. A. Wellner (1993), *Efficient and Adaptive Estimation for
Semiparametric Models*, chapter 2.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Finset Metric Matrix
open scoped Topology ENNReal NNReal

namespace CausalInference

namespace ParametricFamily

variable {S : Type*} [MeasurableSpace S] {p : ℕ}

/-- The one dimensional submodel through `θ₀` in the direction `u`: the scalar family with
density `f(·; θ₀ + t u)` and parameter set `{t | θ₀ + t u ∈ Θ}`. -/
noncomputable def line (F : ParametricFamily (Fin p → ℝ) S) (θ₀ u : Fin p → ℝ) :
    ParametricFamily ℝ S where
  ν := F.ν
  Θ := {t | θ₀ + t • u ∈ F.Θ}
  density t x := F.density (θ₀ + t • u) x
  measurable_density _ := F.measurable_density _
  density_nonneg _ ht x := F.density_nonneg _ ht x
  integrable_density _ ht := F.integrable_density _ ht
  integral_density _ ht := F.integral_density _ ht

variable {F : ParametricFamily (Fin p → ℝ) S} {θ₀ : Fin p → ℝ}

/-- The law of the line at `t` is `P_{θ₀ + t u}`. -/
theorem line_law (u : Fin p → ℝ) (t : ℝ) : (F.line θ₀ u).law t = F.law (θ₀ + t • u) := rfl

/-- At `t = 0` the line has the law `P_θ₀`. -/
theorem line_law_zero (u : Fin p → ℝ) : (F.line θ₀ u).law 0 = F.law θ₀ := by
  rw [line_law, zero_smul, add_zero]

instance [SigmaFinite F.ν] (θ₀ u : Fin p → ℝ) : SigmaFinite (F.line θ₀ u).ν :=
  inferInstanceAs (SigmaFinite F.ν)

/-- The sample family of the line at `t` is the sample family of `F` at `θ₀ + t u`. -/
theorem pi_line_law [SigmaFinite F.ν] (u : Fin p → ℝ) (n : ℕ) (t : ℝ) :
    ((F.line θ₀ u).pi n).law t = (F.pi n).law (θ₀ + t • u) := rfl

/-- The log density of the line is the log density of `F` on the line. -/
theorem line_logLik (u : Fin p → ℝ) (t : ℝ) (x : S) :
    (F.line θ₀ u).logLik t x = F.logLik (θ₀ + t • u) x := rfl

/-- The path `t ↦ θ₀ + t u` has derivative `u`. -/
theorem hasDerivAt_line_path (u : Fin p → ℝ) (t : ℝ) :
    HasDerivAt (fun s : ℝ ↦ θ₀ + s • u) u t := by
  have h := ((hasDerivAt_id t).smul_const u).const_add θ₀
  simpa using h

/-- The path `t ↦ θ₀ + t u` tends to `θ₀` at `0`. -/
theorem tendsto_line_path (u : Fin p → ℝ) :
    Tendsto (fun s : ℝ ↦ θ₀ + s • u) (𝓝 0) (𝓝 θ₀) := by
  have h := ((continuous_const (y := θ₀)).add (continuous_id.smul continuous_const)).tendsto
    (0 : ℝ) (f := fun s : ℝ ↦ θ₀ + s • u)
  simpa using h

/-- For `|t| < ε / (‖u‖ + 1)` the point `θ₀ + t u` lies in `ball θ₀ ε`. -/
theorem line_mem_ball {u : Fin p → ℝ} {ε : ℝ} {t : ℝ}
    (ht : t ∈ ball (0 : ℝ) (ε / (‖u‖ + 1))) : θ₀ + t • u ∈ ball θ₀ ε := by
  have hu : 0 < ‖u‖ + 1 := by positivity
  rw [mem_ball, dist_eq_norm] at ht ⊢
  rw [add_sub_cancel_left, norm_smul]
  rw [sub_zero, lt_div_iff₀ hu] at ht
  nlinarith [norm_nonneg u, norm_nonneg t]

/-! ### Linear and bilinear forms in coordinates -/

/-- A linear form on `ℝ^p` in coordinates: `A u = ∑ k, u k A eₖ`. -/
theorem clm_apply_eq_sum (A : (Fin p → ℝ) →L[ℝ] ℝ) (u : Fin p → ℝ) :
    A u = ∑ k, u k * A (Pi.single k 1) := by
  conv_lhs => rw [eq_gradCLM A]
  rw [gradCLM_apply, dotProduct]
  exact Finset.sum_congr rfl fun k _ ↦ mul_comm _ _

/-- A bilinear form on `ℝ^p` in coordinates: `B u u = ∑ j, ∑ k, u j u k B eⱼ eₖ`. -/
theorem clm_apply_apply_eq_sum (B : (Fin p → ℝ) →L[ℝ] (Fin p → ℝ) →L[ℝ] ℝ)
    (u : Fin p → ℝ) :
    B u u = ∑ j, ∑ k, u j * u k * B (Pi.single j 1) (Pi.single k 1) := by
  rw [clm_apply_eq_sum (B u) u]
  have h : ∀ k, B u (Pi.single k 1) = ∑ j, u j * B (Pi.single j 1) (Pi.single k 1) := fun k ↦ by
    simpa using clm_apply_eq_sum ((ContinuousLinearMap.apply ℝ ℝ (Pi.single k (1 : ℝ))).comp B) u
  simp_rw [h, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun j _ ↦ Finset.sum_congr rfl fun k _ ↦ by ring

/-- `|B u u| ≤ (∑ |u j|)² M` when every entry `B eⱼ eₖ` is bounded by `M`. -/
theorem abs_clm_apply_apply_le {B : (Fin p → ℝ) →L[ℝ] (Fin p → ℝ) →L[ℝ] ℝ} (u : Fin p → ℝ)
    {M : ℝ} (hB : ∀ j k, |B (Pi.single j 1) (Pi.single k 1)| ≤ M) :
    |B u u| ≤ (∑ j, |u j|) ^ 2 * M := by
  rw [clm_apply_apply_eq_sum, sq, Finset.sum_mul_sum, Finset.sum_mul]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ ↦ ?_)
  rw [Finset.sum_mul]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun k _ ↦ ?_)
  rw [abs_mul, abs_mul]
  exact mul_le_mul_of_nonneg_left (hB j k) (by positivity)

/-- `|A u| ≤ (∑ |u k|) M` when every `A eₖ` is bounded by `M`. -/
theorem abs_clm_apply_le {A : (Fin p → ℝ) →L[ℝ] ℝ} (u : Fin p → ℝ) {M : ℝ}
    (hA : ∀ k, |A (Pi.single k 1)| ≤ M) : |A u| ≤ (∑ k, |u k|) * M := by
  rw [clm_apply_eq_sum, Finset.sum_mul]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun k _ ↦ ?_)
  rw [abs_mul]
  exact mul_le_mul_of_nonneg_left (hA k) (abs_nonneg _)

/-! ### Derivatives of the density along a line -/

section Calculus

variable {u : Fin p → ℝ} {ε : ℝ} {x : S}

/-- Where the density is `C²` on an open ball, the partial derivative `∂ₖ f(x; η)` is the
Fréchet derivative applied to `eₖ`. -/
theorem partialDeriv_eq_fderiv (hC : ContDiffOn ℝ 2 (fun η ↦ F.density η x) (ball θ₀ ε))
    {η : Fin p → ℝ} (hη : η ∈ ball θ₀ ε) (k : Fin p) :
    F.partialDeriv k η x = fderiv ℝ (fun η ↦ F.density η x) η (Pi.single k 1) := by
  have h := hasDerivAt_slice_of_contDiffOn hC (η := η) k (t := η k) (by simpa using hη)
  simp only [Function.update_eq_self] at h
  exact h.deriv

/-- The derivative of `fun η ↦ f(x; η)` is differentiable on the ball where the density is
`C²`. -/
theorem hasFDerivAt_fderiv_density (hC : ContDiffOn ℝ 2 (fun η ↦ F.density η x) (ball θ₀ ε))
    {η : Fin p → ℝ} (hη : η ∈ ball θ₀ ε) :
    HasFDerivAt (fderiv ℝ fun η ↦ F.density η x)
      (fderiv ℝ (fderiv ℝ fun η ↦ F.density η x) η) η :=
  (((hC.fderiv_of_isOpen isOpen_ball (m := 1) (by norm_num)).differentiableOn
    (by norm_num)).differentiableAt (isOpen_ball.mem_nhds hη)).hasFDerivAt

/-- Where the density is `C²` on an open ball, the second partial derivative
`∂ⱼ ∂ₖ f(x; η)` is the second Fréchet derivative applied to `eⱼ` and `eₖ`. -/
theorem partialDeriv2_eq_fderiv (hC : ContDiffOn ℝ 2 (fun η ↦ F.density η x) (ball θ₀ ε))
    {η : Fin p → ℝ} (hη : η ∈ ball θ₀ ε) (j k : Fin p) :
    F.partialDeriv2 j k η x =
      fderiv ℝ (fderiv ℝ fun η ↦ F.density η x) η (Pi.single j 1) (Pi.single k 1) := by
  set g : (Fin p → ℝ) → ℝ := fun η ↦ F.density η x with hg
  have hpart : (fun t ↦ F.partialDeriv k (Function.update η j t) x) =ᶠ[𝓝 (η j)]
      fun t ↦ fderiv ℝ g (Function.update η j t) (Pi.single k 1) := by
    filter_upwards [(tendsto_update η j).eventually (isOpen_ball.mem_nhds hη)] with t ht
    exact partialDeriv_eq_fderiv hC ht k
  have h1 := (hasFDerivAt_fderiv_density hC hη).comp_hasDerivAt_of_eq (η j)
    (hasDerivAt_update η j (η j)) (Function.update_eq_self j η).symm
  have h2 := ((ContinuousLinearMap.apply ℝ ℝ (Pi.single k (1 : ℝ))).hasFDerivAt).comp_hasDerivAt
    (η j) h1
  exact (h2.congr_of_eventuallyEq hpart).deriv

/-- Along the line, the density has derivative `D f(x; θ₀ + t u) u`. -/
theorem hasDerivAt_line_density (hC : ContDiffOn ℝ 2 (fun η ↦ F.density η x) (ball θ₀ ε))
    {t : ℝ} (ht : θ₀ + t • u ∈ ball θ₀ ε) :
    HasDerivAt (fun s ↦ F.density (θ₀ + s • u) x)
      (fderiv ℝ (fun η ↦ F.density η x) (θ₀ + t • u) u) t := by
  have hd : HasFDerivAt (fun η ↦ F.density η x)
      (fderiv ℝ (fun η ↦ F.density η x) (θ₀ + t • u)) (θ₀ + t • u) :=
    ((hC.differentiableOn (by norm_num)).differentiableAt (isOpen_ball.mem_nhds ht)).hasFDerivAt
  exact hd.comp_hasDerivAt t (hasDerivAt_line_path u t)

/-- The derivative of the density of the line. -/
theorem line_densityDeriv_eq (hC : ContDiffOn ℝ 2 (fun η ↦ F.density η x) (ball θ₀ ε))
    {t : ℝ} (ht : θ₀ + t • u ∈ ball θ₀ ε) :
    (F.line θ₀ u).densityDeriv t x = fderiv ℝ (fun η ↦ F.density η x) (θ₀ + t • u) u :=
  (hasDerivAt_line_density hC ht).deriv

/-- Points of the line near a point of the open ball stay in the ball. -/
theorem eventually_line_mem_ball {t : ℝ} (ht : θ₀ + t • u ∈ ball θ₀ ε) :
    ∀ᶠ s in 𝓝 t, θ₀ + s • u ∈ ball θ₀ ε :=
  (hasDerivAt_line_path (θ₀ := θ₀) u t).continuousAt.preimage_mem_nhds
    (isOpen_ball.mem_nhds ht)

/-- The second derivative of the density of the line is `D² f(x; θ₀ + t u) u u`. -/
theorem line_densityDeriv2_eq (hC : ContDiffOn ℝ 2 (fun η ↦ F.density η x) (ball θ₀ ε))
    {t : ℝ} (ht : θ₀ + t • u ∈ ball θ₀ ε) :
    (F.line θ₀ u).densityDeriv2 t x =
      fderiv ℝ (fderiv ℝ fun η ↦ F.density η x) (θ₀ + t • u) u u := by
  have hev : (fun s ↦ (F.line θ₀ u).densityDeriv s x) =ᶠ[𝓝 t]
      fun s ↦ fderiv ℝ (fun η ↦ F.density η x) (θ₀ + s • u) u := by
    filter_upwards [eventually_line_mem_ball ht] with s hs
    exact line_densityDeriv_eq hC hs
  have h2 := ((ContinuousLinearMap.apply ℝ ℝ u).hasFDerivAt.comp _
    (hasFDerivAt_fderiv_density hC ht)).comp_hasDerivAt t (hasDerivAt_line_path (θ₀ := θ₀) u t)
  rw [densityDeriv2, hev.deriv_eq]
  exact h2.deriv

end Calculus

/-! ### The score and the information of a line -/

/-- **The second moments of linear combinations of the score**: for a square integrable score,
`E_θ₀[(aᵀ s)(bᵀ s)] = aᵀ I(θ₀) b`. -/
theorem integral_dotProduct_scoreVec_mul
    (hs : ∀ j, MemLp (fun x ↦ F.scoreVec θ₀ x j) 2 (F.law θ₀)) (a b : Fin p → ℝ) :
    ∫ x, (a ⬝ᵥ F.scoreVec θ₀ x) * (b ⬝ᵥ F.scoreVec θ₀ x) ∂F.law θ₀ =
      a ⬝ᵥ (F.fisherInfoMatrix θ₀ *ᵥ b) := by
  have hprod : ∀ j k, Integrable (fun x ↦ F.scoreVec θ₀ x j * F.scoreVec θ₀ x k) (F.law θ₀) :=
    fun j k ↦ (hs j).integrable_mul (hs k)
  have e : (fun x ↦ (a ⬝ᵥ F.scoreVec θ₀ x) * (b ⬝ᵥ F.scoreVec θ₀ x)) =
      fun x ↦ ∑ j, ∑ k, a j * b k * (F.scoreVec θ₀ x j * F.scoreVec θ₀ x k) := by
    funext x
    simp only [dotProduct, Finset.sum_mul_sum]
    exact Finset.sum_congr rfl fun j _ ↦ Finset.sum_congr rfl fun k _ ↦ by ring
  rw [e, integral_finsetSum _ fun j _ ↦ integrable_finsetSum _ fun k _ ↦
    (hprod j k).const_mul _]
  simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [integral_finsetSum _ fun k _ ↦ (hprod j k).const_mul _]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  rw [integral_const_mul]
  simp only [fisherInfoMatrix, Matrix.of_apply]
  ring

/-- A linear combination `aᵀ s(θ₀; ·)` of a square integrable score is square integrable. -/
theorem memLp_dotProduct_scoreVec
    (hs : ∀ j, MemLp (fun x ↦ F.scoreVec θ₀ x j) 2 (F.law θ₀)) (a : Fin p → ℝ) :
    MemLp (fun x ↦ a ⬝ᵥ F.scoreVec θ₀ x) 2 (F.law θ₀) := by
  simp only [dotProduct]
  exact memLp_finsetSum _ fun j _ ↦ (hs j).const_mul (a j)

/-- **The score of a line.** At a regular point, the score of the line through `θ₀` in the
direction `u` at `t = 0` is `uᵀ s(θ₀; ·)`, `P_θ₀`-almost surely. -/
theorem line_score_zero_ae (hreg : F.IsRegularAtVec θ₀) (u : Fin p → ℝ) :
    ∀ᵐ x ∂F.law θ₀, (F.line θ₀ u).score 0 x = u ⬝ᵥ F.scoreVec θ₀ x := by
  obtain ⟨ε, hε, -, hC, -⟩ := hreg.smooth_dominated
  filter_upwards [ae_law_of_ae hC] with x hx
  have h0 : θ₀ + (0 : ℝ) • u ∈ ball θ₀ ε := by
    simpa using (mem_ball_self hε : θ₀ ∈ ball θ₀ ε)
  rw [score, line_densityDeriv_eq hx h0, clm_apply_eq_sum, dotProduct, Finset.sum_div]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  simp only [zero_smul, add_zero, scoreVec, partialDeriv_eq_fderiv hx (mem_ball_self hε) k]
  change _ / F.density (θ₀ + (0 : ℝ) • u) x = _
  rw [zero_smul, add_zero]
  ring

/-- **The information of a line.** At a regular point, the information of the line through
`θ₀` in the direction `u` at `t = 0` is `uᵀ I(θ₀) u`. -/
theorem line_fisherInfo (hreg : F.IsRegularAtVec θ₀) (u : Fin p → ℝ) :
    (F.line θ₀ u).fisherInfo 0 = u ⬝ᵥ (F.fisherInfoMatrix θ₀ *ᵥ u) := by
  rw [fisherInfo, line_law_zero, integral_congr_ae ((line_score_zero_ae hreg u).mono
    fun x hx ↦ by rw [hx])]
  simp_rw [sq]
  exact integral_dotProduct_scoreVec_mul hreg.memLp_scoreVec u u

/-- With positive definite information, every line in a direction `u ≠ 0` has positive
information. -/
theorem line_fisherInfo_pos (hreg : F.IsRegularAtVec θ₀) (hI : (F.fisherInfoMatrix θ₀).PosDef)
    {u : Fin p → ℝ} (hu : u ≠ 0) : 0 < (F.line θ₀ u).fisherInfo 0 := by
  rw [line_fisherInfo hreg]
  simpa using hI.dotProduct_mulVec_pos hu

/-! ### Regularity of a line -/

/-- **A regular point of a vector family is a regular point of every line through it.** The
support of the line is that of `F` near `θ₀`; on the ball of radius `ε / (‖u‖ + 1)` the line
density is `C²` with envelopes `(∑ₖ |uₖ|) b₁` and `(∑ₖ |uₖ|)² b₂` of its first two derivatives;
the score `uᵀ s(θ₀; ·)` is square integrable. -/
theorem IsRegularAtVec.line_isRegularAt (hreg : F.IsRegularAtVec θ₀) (u : Fin p → ℝ) :
    (F.line θ₀ u).IsRegularAt 0 := by
  obtain ⟨ε, hε, hball, hC, b₁, b₂, hb₁, hb₂, hbd⟩ := hreg.smooth_dominated
  have hδ : 0 < ε / (‖u‖ + 1) := by positivity
  have hmem : ∀ t ∈ ball (0 : ℝ) (ε / (‖u‖ + 1)), θ₀ + t • u ∈ ball θ₀ ε :=
    fun t ht ↦ line_mem_ball ht
  refine ⟨?_, ⟨ε / (‖u‖ + 1), hδ, fun t ht ↦ hball (hmem t ht), ?_,
    fun x ↦ (∑ k, |u k|) * b₁ x, fun x ↦ (∑ j, |u j|) ^ 2 * b₂ x, hb₁.const_mul _,
    hb₂.const_mul _, ?_⟩, ?_⟩
  · filter_upwards [tendsto_line_path (θ₀ := θ₀) u hreg.support] with t ht x
    change 0 < F.density (θ₀ + t • u) x ↔ 0 < F.density (θ₀ + (0 : ℝ) • u) x
    rw [zero_smul, add_zero]
    exact ht x
  · filter_upwards [hC] with x hx
    exact hx.comp (contDiff_const.add (contDiff_id.smul contDiff_const)).contDiffOn
      fun t ht ↦ hmem t ht
  · filter_upwards [hC, hbd] with x hx hb t ht
    rw [line_densityDeriv_eq hx (hmem t ht), line_densityDeriv2_eq hx (hmem t ht)]
    refine ⟨abs_clm_apply_le u fun k ↦ ?_, abs_clm_apply_apply_le u fun j k ↦ ?_⟩
    · rw [← partialDeriv_eq_fderiv hx (hmem t ht)]
      exact (hb _ (hmem t ht) k k).1
    · rw [← partialDeriv2_eq_fderiv hx (hmem t ht)]
      exact (hb _ (hmem t ht) j k).2
  · have hae : (F.line θ₀ u).score 0 =ᵐ[F.law θ₀] fun x ↦ u ⬝ᵥ F.scoreVec θ₀ x :=
      line_score_zero_ae hreg u
    rw [line_law_zero]
    exact (memLp_dotProduct_scoreVec hreg.memLp_scoreVec u).ae_eq hae.symm

/-! ### Smoothness of the score of a line -/

/-- **The calculus of the log density along a line.** If `η ↦ f(x; η)` is `C²` and positive on
`ball θ₀ ε` and `θ₀ + t u` lies in that ball, then at `t` the log density of the line has
derivative the score of the line, the score of the line has derivative the second derivative of
its log density, and that second derivative is `D² ℓ(θ₀ + t u; x) u u`. -/
theorem line_score_calculus {u : Fin p → ℝ} {ε : ℝ} {x : S}
    (hC : ContDiffOn ℝ 2 (fun η ↦ F.density η x) (ball θ₀ ε))
    (hpos : ∀ η ∈ ball θ₀ ε, 0 < F.density η x) {t : ℝ} (ht : θ₀ + t • u ∈ ball θ₀ ε) :
    HasDerivAt (fun s ↦ (F.line θ₀ u).logLik s x) ((F.line θ₀ u).score t x) t ∧
      HasDerivAt (fun s ↦ (F.line θ₀ u).score s x) ((F.line θ₀ u).hessLogLik t x) t ∧
      (F.line θ₀ u).hessLogLik t x =
        fderiv ℝ (fderiv ℝ fun η ↦ F.logLik η x) (θ₀ + t • u) u u := by
  obtain ⟨-, hLd, hGd, -, -⟩ := logLik_calculus hC hpos
  set G := fderiv ℝ fun η ↦ F.logLik η x with hG
  have hscore : ∀ s, θ₀ + s • u ∈ ball θ₀ ε → (F.line θ₀ u).score s x = G (θ₀ + s • u) u := by
    intro s hs
    have hd : HasFDerivAt (fun η ↦ F.density η x)
        (fderiv ℝ (fun η ↦ F.density η x) (θ₀ + s • u)) (θ₀ + s • u) :=
      ((hC.differentiableOn (by norm_num)).differentiableAt (isOpen_ball.mem_nhds hs)).hasFDerivAt
    have hu : G (θ₀ + s • u) = (F.density (θ₀ + s • u) x)⁻¹ •
        fderiv ℝ (fun η ↦ F.density η x) (θ₀ + s • u) :=
      (hLd _ hs).unique (hd.log (hpos _ hs).ne')
    rw [score, line_densityDeriv_eq hC hs, hu, smul_apply, smul_eq_mul,
      div_eq_inv_mul]
    rfl
  have h1 : ∀ s, θ₀ + s • u ∈ ball θ₀ ε →
      HasDerivAt (fun v ↦ (F.line θ₀ u).logLik v x) ((F.line θ₀ u).score s x) s := by
    intro s hs
    rw [hscore s hs]
    exact (hLd _ hs).comp_hasDerivAt s (hasDerivAt_line_path u s)
  have h2 : HasDerivAt (fun s ↦ (F.line θ₀ u).score s x)
      (fderiv ℝ G (θ₀ + t • u) u u) t := by
    have h := ((ContinuousLinearMap.apply ℝ ℝ u).hasFDerivAt.comp _
      (hGd _ ht)).comp_hasDerivAt t (hasDerivAt_line_path (θ₀ := θ₀) u t)
    refine HasDerivAt.congr_of_eventuallyEq h ?_
    filter_upwards [eventually_line_mem_ball ht] with s hs
    exact hscore s hs
  have h3 : (F.line θ₀ u).hessLogLik t x = fderiv ℝ G (θ₀ + t • u) u u := by
    have e : (fun s ↦ deriv (fun v ↦ (F.line θ₀ u).logLik v x) s) =ᶠ[𝓝 t]
        fun s ↦ (F.line θ₀ u).score s x := by
      filter_upwards [eventually_line_mem_ball ht] with s hs
      exact (h1 s hs).deriv
    rw [hessLogLik, e.deriv_eq, h2.deriv]
  exact ⟨h1 t ht, h3 ▸ h2, h3⟩

/-- **Smoothness of the score passes to a line.** At a regular point `θ₀` of `F` whose score is
regular on a closed ball (`IsScoreRegularVec θ₀ r`), the line through `θ₀` in the direction `u`
satisfies `IsScoreRegular 0 r'` for some `r' > 0`, with `∂_t ℓ_line(t; z) = s_line(t; z)` on the
closed ball of radius `r'`, provided the score of the line at `0` and the second derivatives of
its log density near `0` are measurable. On the closed ball the second derivative is
`uᵀ ∂²ℓ(θ₀ + t u; z) u`, with envelope `(∑ⱼ |uⱼ|)² H` for an envelope `H` of the Hessian
entries.

The measurability hypotheses are assumed because they concern functions defined everywhere
that the hypotheses on `F` identify only almost everywhere; on a discrete sample space they hold
(`line_isScoreRegular_of_discrete`). -/
theorem line_isScoreRegular (hreg : F.IsRegularAtVec θ₀) {r : ℝ} (hs : F.IsScoreRegularVec θ₀ r)
    (u : Fin p → ℝ) (hms : Measurable ((F.line θ₀ u).score 0))
    (hmh : ∀ᶠ t in 𝓝 (0 : ℝ), Measurable ((F.line θ₀ u).hessLogLik t)) :
    ∃ r' > 0, (F.line θ₀ u).IsScoreRegular 0 r' ∧
      ∀ᵐ z ∂(F.line θ₀ u).law 0, ∀ t ∈ closedBall (0 : ℝ) r',
        HasDerivAt (fun s ↦ (F.line θ₀ u).logLik s z) ((F.line θ₀ u).score t z) t := by
  obtain ⟨ε, hε, -, hC, hpos⟩ := hreg.exists_ball_pos
  obtain ⟨H, hH, hHb⟩ := hs.dominated
  obtain ⟨ρ, hρ, hρm⟩ := Metric.eventually_nhds_iff.1 hmh
  have hR : 0 < min ε r := lt_min hε hs.pos
  have hδ : 0 < min ε r / (‖u‖ + 1) := by positivity
  have hm : 0 < min (min ε r / (‖u‖ + 1)) ρ := lt_min hδ hρ
  set r' := min (min ε r / (‖u‖ + 1)) ρ / 2 with hr'
  have hr'0 : 0 < r' := half_pos hm
  have hlt : r' < min (min ε r / (‖u‖ + 1)) ρ := half_lt_self hm
  have hsub : closedBall (0 : ℝ) r' ⊆ ball 0 (min ε r / (‖u‖ + 1)) :=
    closedBall_subset_ball (hlt.trans_le (min_le_left _ _))
  have hsubρ : closedBall (0 : ℝ) r' ⊆ ball 0 ρ :=
    closedBall_subset_ball (hlt.trans_le (min_le_right _ _))
  have hRε : ball θ₀ (min ε r) ⊆ ball θ₀ ε := ball_subset_ball (min_le_left _ _)
  have hRr : ball θ₀ (min ε r) ⊆ closedBall θ₀ r :=
    (ball_subset_ball (min_le_right _ _)).trans ball_subset_closedBall
  have hmem : ∀ t ∈ closedBall (0 : ℝ) r', θ₀ + t • u ∈ ball θ₀ (min ε r) :=
    fun t ht ↦ line_mem_ball (hsub ht)
  have hgood : ∀ᵐ z ∂F.law θ₀, ContDiffOn ℝ 2 (fun η ↦ F.density η z) (ball θ₀ ε) ∧
      (∀ η ∈ ball θ₀ ε, 0 < F.density η z) ∧
      ∀ θ ∈ closedBall θ₀ r, ∀ j k, |F.hessianLogLik j k θ z| ≤ H z := by
    filter_upwards [hC, hpos, hHb] with z h1 h2 h3
    exact ⟨h1, h2, h3⟩
  refine ⟨r', hr'0, ⟨hr'0, hms, fun t ht ↦ hρm (hsubρ ht), ?_, ?_,
    ⟨fun z ↦ (∑ j, |u j|) ^ 2 * H z, ?_, ?_⟩⟩, ?_⟩
  · rw [line_law_zero]
    filter_upwards [hgood] with z hz t ht
    exact (line_score_calculus hz.1 hz.2.1 (hRε (hmem t ht))).2.1
  · rw [line_law_zero]
    filter_upwards [hgood] with z hz
    obtain ⟨hc, -⟩ := logLik_calculus hz.1 hz.2.1
    have hpath : Continuous fun t : ℝ ↦ θ₀ + t • u := by fun_prop
    have h : ContinuousOn
        (fun t : ℝ ↦ fderiv ℝ (fderiv ℝ fun η ↦ F.logLik η z) (θ₀ + t • u) u u)
        (closedBall 0 r') :=
      ((hc.comp hpath.continuousOn fun t ht ↦ hRε (hmem t ht)).clm_apply
        continuousOn_const).clm_apply continuousOn_const
    exact h.congr fun t ht ↦ (line_score_calculus hz.1 hz.2.1 (hRε (hmem t ht))).2.2
  · rw [line_law_zero]
    exact hH.const_mul _
  · rw [line_law_zero]
    filter_upwards [hgood] with z hz t ht
    obtain ⟨-, -, -, -, hh⟩ := logLik_calculus hz.1 hz.2.1
    rw [(line_score_calculus hz.1 hz.2.1 (hRε (hmem t ht))).2.2]
    refine abs_clm_apply_apply_le u fun j k ↦ ?_
    rw [← hh _ (hRε (hmem t ht)) j k]
    exact hz.2.2 _ (hRr (hmem t ht)) j k
  · rw [line_law_zero]
    filter_upwards [hgood] with z hz t ht
    exact (line_score_calculus hz.1 hz.2.1 (hRε (hmem t ht))).1

/-- On a discrete sample space the measurability hypotheses of `line_isScoreRegular` hold. -/
theorem line_isScoreRegular_of_discrete [DiscreteMeasurableSpace S]
    (hreg : F.IsRegularAtVec θ₀) {r : ℝ} (hs : F.IsScoreRegularVec θ₀ r) (u : Fin p → ℝ) :
    ∃ r' > 0, (F.line θ₀ u).IsScoreRegular 0 r' ∧
      ∀ᵐ z ∂(F.line θ₀ u).law 0, ∀ t ∈ closedBall (0 : ℝ) r',
        HasDerivAt (fun s ↦ (F.line θ₀ u).logLik s z) ((F.line θ₀ u).score t z) t :=
  line_isScoreRegular hreg hs u .of_discrete (Eventually.of_forall fun _ ↦ .of_discrete)

end ParametricFamily

end CausalInference
