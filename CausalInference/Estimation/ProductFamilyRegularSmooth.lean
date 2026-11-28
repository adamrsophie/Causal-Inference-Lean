/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.Estimation.ProductFamilyRegular
public import CausalInference.Estimation.HajekRegularLinear
public import CausalInference.Estimation.NormalLocationFamily

/-!
# Regularity of the sample family from pointwise smoothness

`CausalInference.ParametricFamily.pi_isScoreRegular` transfers `IsScoreRegular` to the sample
family `F.pi n`, but it assumes measurability of the sample score and of the second derivative of
the sample log likelihood, which are hypotheses on `F.pi n`. Here the regularity of `F` is assumed
at every observation on an open ball (`IsSmoothOnBall`): the density is positive and the log
density is twice differentiable with derivatives `s(θ; x)` and `∂²ℓ(θ; x)`. Then the sample score
and the sample second derivative are sums over the coordinates at every sample, so their
measurability follows from that of `F`, and every hypothesis of the asymptotic theory for
`F.pi n` follows from hypotheses on `F` alone, on any sample space.

## Main results

* `IsSmoothOnBall`: pointwise smoothness of `F` on a ball; `IsSmoothOnBall.pi` passes it to the
  sample family.
* `pi_isScoreRegular_of_isSmoothOnBall`: `F.pi n` satisfies `IsScoreRegular θ₀ r` on the same
  radius, with the derivative identity at every sample.
* `pi_regularity_of_isSmoothOnBall`: regularity, smoothness of the score, the derivative identity
  and the information `n I(θ₀)` for `F.pi n`.
* `pi_exists_isHajekRegular_iff_of_isSmoothOnBall`, `pi_inv_le_integral_sq_of_isSmoothOnBall`:
  the regularity criterion `E[φ s_n] = 1` and the bound `(n I(θ₀))⁻¹ ≤ E[φ²]` for estimators
  built on i.i.d. blocks of `n` observations.
* `normalLocation_pi_regularity`: the instance for the normal location family, whose sample space
  `ℝ` is not discrete; its sample family has information `n`.
* `realSampleMean_isHajekRegular`, `realSampleMean_attains_bound`: in the normal location family
  the sample mean has `E[φ s] = 1`, hence is regular with limit `N(0, 1)`, and its limit variance
  `1` is the bound `I(θ₀)⁻¹`.

## References

* A. W. van der Vaart, *Asymptotic Statistics*, Cambridge University Press (1998), chapters 7
  and 8.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Finset Metric
open scoped Topology ENNReal NNReal

namespace CausalInference

namespace ParametricFamily

variable {S : Type*} [MeasurableSpace S] {F : ParametricFamily ℝ S} [SigmaFinite F.ν] {θ₀ : ℝ}

/-- **Pointwise smoothness on a ball.** For every observation `x` and every `θ` in the open ball
of radius `ρ` around `θ₀`: the density is positive, the log density has derivative `s(θ; x)` and
the score has derivative `∂²ℓ(θ; x)`. Unlike `IsScoreRegular`, this holds for every `x`, not only
almost every `x`. -/
def IsSmoothOnBall (F : ParametricFamily ℝ S) (θ₀ ρ : ℝ) : Prop :=
  ∀ x, ∀ θ ∈ ball θ₀ ρ, 0 < F.density θ x ∧
    HasDerivAt (fun u ↦ F.logLik u x) (F.score θ x) θ ∧
    HasDerivAt (fun u ↦ F.score u x) (F.hessLogLik θ x) θ

namespace IsSmoothOnBall

variable {ρ : ℝ}

omit [SigmaFinite F.ν] in
/-- Pointwise smoothness gives the derivative identity of the log density almost everywhere on
every closed ball inside the open ball. -/
theorem ae_hasDerivAt_logLik (h : F.IsSmoothOnBall θ₀ ρ) {r : ℝ} (hr : r < ρ) :
    ∀ᵐ z ∂F.law θ₀, ∀ θ ∈ closedBall θ₀ r,
      HasDerivAt (fun u ↦ F.logLik u z) (F.score θ z) θ :=
  ae_of_all _ fun z θ hθ ↦ (h z θ (closedBall_subset_ball hr hθ)).2.1

/-- The sample score and the second derivative of the sample log likelihood are sums over the
coordinates at every sample and every point of the ball. -/
theorem pi_eq_sum (h : F.IsSmoothOnBall θ₀ ρ) (n : ℕ) (x : Fin n → S) {θ : ℝ}
    (hθ : θ ∈ ball θ₀ ρ) :
    HasDerivAt (fun u ↦ (F.pi n).logLik u x) ((F.pi n).score θ x) θ ∧
      (F.pi n).score θ x = ∑ i, F.score θ (x i) ∧
      HasDerivAt (fun u ↦ (F.pi n).score u x) ((F.pi n).hessLogLik θ x) θ ∧
      (F.pi n).hessLogLik θ x = ∑ i, F.hessLogLik θ (x i) :=
  pi_score_hasDerivAt_of_isOpen isOpen_ball (fun i u hu ↦ (h (x i) u hu).1)
    (fun i u hu ↦ (h (x i) u hu).2.1) (fun i u hu ↦ (h (x i) u hu).2.2) hθ

/-- Pointwise smoothness passes to the sample family, on the same ball. -/
theorem pi (h : F.IsSmoothOnBall θ₀ ρ) (n : ℕ) : (F.pi n).IsSmoothOnBall θ₀ ρ := by
  intro x θ hθ
  obtain ⟨h1, -, h3, -⟩ := h.pi_eq_sum n x hθ
  refine ⟨?_, h1, h3⟩
  rw [pi_density]
  exact Finset.prod_pos fun i _ ↦ (h (x i) θ hθ).1

end IsSmoothOnBall

/-- **Smoothness of the score passes to the sample family, with hypotheses on `F` only.** If `F`
satisfies `IsScoreRegular θ₀ r` and is pointwise smooth (`IsSmoothOnBall`) on an open ball of
radius `ρ > r`, then the sample family `F.pi n` satisfies `IsScoreRegular θ₀ r` on the same
radius, and its log likelihood has derivative equal to its score at every sample and every point
of the closed ball. The measurability of the sample score and of the second derivative of the
sample log likelihood follows from that of `F`, since both are sums over the coordinates at every
sample. -/
theorem pi_isScoreRegular_of_isSmoothOnBall (n : ℕ) (hθ₀ : θ₀ ∈ F.Θ) {r ρ : ℝ}
    (hs : F.IsScoreRegular θ₀ r) (hrρ : r < ρ) (hsm : F.IsSmoothOnBall θ₀ ρ) :
    (F.pi n).IsScoreRegular θ₀ r ∧ ∀ x, ∀ θ ∈ closedBall θ₀ r,
      HasDerivAt (fun u ↦ (F.pi n).logLik u x) ((F.pi n).score θ x) θ := by
  have := isProbabilityMeasure_law hθ₀
  have hsub : closedBall θ₀ r ⊆ ball θ₀ ρ := closedBall_subset_ball hrρ
  have hc : θ₀ ∈ closedBall θ₀ r := mem_closedBall_self hs.pos.le
  obtain ⟨H, hH, hHb⟩ := hs.dominated
  have hgood : ∀ᵐ x ∂(F.pi n).law θ₀, ∀ i,
      ContinuousOn (fun u ↦ F.hessLogLik u (x i)) (closedBall θ₀ r) ∧
      ∀ θ ∈ closedBall θ₀ r, |F.hessLogLik θ (x i)| ≤ H (x i) := by
    rw [pi_law n hθ₀]
    exact ae_all_iff.2 fun i ↦ (Measure.tendsto_eval_ae_ae (μ := fun _ : Fin n ↦ F.law θ₀)
      (i := i)).eventually (hs.continuousOn_hessLogLik.and hHb)
  refine ⟨⟨hs.pos, ?_, fun θ hθ ↦ ?_, ?_, ?_, ⟨fun x ↦ ∑ i, H (x i), ?_, ?_⟩⟩,
    fun x θ hθ ↦ (hsm.pi_eq_sum n x (hsub hθ)).1⟩
  · have e : (F.pi n).score θ₀ = fun x ↦ ∑ i, F.score θ₀ (x i) :=
      funext fun x ↦ (hsm.pi_eq_sum n x (hsub hc)).2.1
    rw [e]
    exact Finset.measurable_sum _ fun i _ ↦ hs.measurable_score.comp (measurable_pi_apply i)
  · have e : (F.pi n).hessLogLik θ = fun x ↦ ∑ i, F.hessLogLik θ (x i) :=
      funext fun x ↦ (hsm.pi_eq_sum n x (hsub hθ)).2.2.2
    rw [e]
    exact Finset.measurable_sum _ fun i _ ↦
      (hs.measurable_hessLogLik θ hθ).comp (measurable_pi_apply i)
  · exact ae_of_all _ fun x θ hθ ↦ (hsm.pi_eq_sum n x (hsub hθ)).2.2.1
  · filter_upwards [hgood] with x hx
    exact (continuousOn_finsetSum univ fun i _ ↦ (hx i).1).congr
      fun θ hθ ↦ (hsm.pi_eq_sum n x (hsub hθ)).2.2.2
  · rw [pi_law n hθ₀]
    exact integrable_finsetSum _ fun i _ ↦
      (measurePreserving_eval (fun _ : Fin n ↦ F.law θ₀) i).integrable_comp_of_integrable hH
  · filter_upwards [hgood] with x hx θ hθ
    rw [(hsm.pi_eq_sum n x (hsub hθ)).2.2.2]
    exact (Finset.abs_sum_le_sum_abs _ _).trans
      (Finset.sum_le_sum fun i _ ↦ (hx i).2 θ hθ)

/-- **The hypotheses of the asymptotic theory for a sample family, from `F` alone.** If `F` is
regular at `θ₀`, satisfies `IsScoreRegular θ₀ r`, and is pointwise smooth on an open ball of
radius `ρ > r`, then the sample family `F.pi n` is regular at `θ₀`, satisfies
`IsScoreRegular θ₀ r`, has log likelihood derivative equal to its score on the closed ball
(almost surely under `(F.pi n).law θ₀`, as the theorems of `HajekRegularLinear` require), and has
information `n I(θ₀)`. No hypothesis mentions `F.pi n`, and `S` is arbitrary. -/
theorem pi_regularity_of_isSmoothOnBall (n : ℕ) (hreg : F.IsRegularAt θ₀) {r ρ : ℝ}
    (hs : F.IsScoreRegular θ₀ r) (hrρ : r < ρ) (hsm : F.IsSmoothOnBall θ₀ ρ) :
    (F.pi n).IsRegularAt θ₀ ∧ (F.pi n).IsScoreRegular θ₀ r ∧
      (∀ᵐ x ∂(F.pi n).law θ₀, ∀ θ ∈ closedBall θ₀ r,
        HasDerivAt (fun u ↦ (F.pi n).logLik u x) ((F.pi n).score θ x) θ) ∧
      (F.pi n).fisherInfo θ₀ = n * F.fisherInfo θ₀ := by
  obtain ⟨h1, h2⟩ := pi_isScoreRegular_of_isSmoothOnBall n (mem_of_mem_nhds hreg.mem_nhds) hs
    hrρ hsm
  exact ⟨pi_isRegularAt n hreg, h1, ae_of_all _ h2, pi_fisherInfo_of_isRegularAt n hreg⟩

/-! ### Estimators built on blocks of `n` observations -/

/-- The dominating measure `ν^n` of the sample family is σ-finite. -/
instance sigmaFinite_pi_ν (n : ℕ) : SigmaFinite (F.pi n).ν :=
  inferInstanceAs (SigmaFinite (Measure.pi fun _ : Fin n ↦ F.ν))

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- **The regularity criterion for estimators built on blocks.** Let the observations be i.i.d.
blocks `O m` of `n ≥ 1` observations of `F`, with law `(F.pi n).law θ₀`, and let `T` be
asymptotically linear in the blocks with influence function `φ`. Under the hypotheses on `F` of
`pi_regularity_of_isSmoothOnBall` and `I(θ₀) > 0`, `T` is regular in the block family if and only
if `E[φ s_n] = 1`, with `s_n` the score of a block. -/
theorem pi_exists_isHajekRegular_iff_of_isSmoothOnBall {n : ℕ} (hn : 0 < n)
    {O : ℕ → Ω → Fin n → S} (hO : IsIIDSample O μ) (hlaw : μ.map (O 0) = (F.pi n).law θ₀)
    (hreg : F.IsRegularAt θ₀) {r ρ : ℝ} (hs : F.IsScoreRegular θ₀ r) (hrρ : r < ρ)
    (hsm : F.IsSmoothOnBall θ₀ ρ) (hI : 0 < F.fisherInfo θ₀)
    {T : ∀ m, (Fin m → Fin n → S) → ℝ} (hTm : ∀ m, Measurable (T m)) {φ : (Fin n → S) → ℝ}
    (hlin : IsAsymptoticallyLinear (fun m ω ↦ T m fun i ↦ O i ω) θ₀ φ O μ) :
    (∃ L : Measure ℝ, (F.pi n).IsHajekRegular T θ₀ L) ↔
      ∫ x, φ x * (F.pi n).score θ₀ x ∂(F.pi n).law θ₀ = 1 := by
  obtain ⟨h1, h2, h3, -⟩ := pi_regularity_of_isSmoothOnBall n hreg hs hrρ hsm
  exact exists_isHajekRegular_iff_integral_mul_score_eq_one hO hlaw h1 h2 h3
    (pi_fisherInfo_pos hn hreg hI) hTm hlin

/-- **The Hájek bound for estimators built on blocks.** Under the hypotheses of
`pi_exists_isHajekRegular_iff_of_isSmoothOnBall`, a regular block estimator has
`(n I(θ₀))⁻¹ ≤ E[φ²]`. -/
theorem pi_inv_le_integral_sq_of_isSmoothOnBall {n : ℕ} (hn : 0 < n)
    {O : ℕ → Ω → Fin n → S} (hO : IsIIDSample O μ) (hlaw : μ.map (O 0) = (F.pi n).law θ₀)
    (hreg : F.IsRegularAt θ₀) {r ρ : ℝ} (hs : F.IsScoreRegular θ₀ r) (hrρ : r < ρ)
    (hsm : F.IsSmoothOnBall θ₀ ρ) (hI : 0 < F.fisherInfo θ₀)
    {T : ∀ m, (Fin m → Fin n → S) → ℝ} (hTm : ∀ m, Measurable (T m)) {φ : (Fin n → S) → ℝ}
    (hlin : IsAsymptoticallyLinear (fun m ω ↦ T m fun i ↦ O i ω) θ₀ φ O μ)
    (hT : ∃ L : Measure ℝ, (F.pi n).IsHajekRegular T θ₀ L) :
    ((n : ℝ) * F.fisherInfo θ₀)⁻¹ ≤ ∫ x, φ x ^ 2 ∂(F.pi n).law θ₀ := by
  obtain ⟨h1, h2, h3, h4⟩ := pi_regularity_of_isSmoothOnBall n hreg hs hrρ hsm
  rw [← h4]
  exact inv_fisherInfo_le_integral_sq_of_isHajekRegular hO hlaw h1 h2 h3
    (pi_fisherInfo_pos hn hreg hI) hTm hlin hT

/-! ### Instance: the normal location family -/

/-- The normal location family is pointwise smooth on every ball. -/
theorem normalLocation_isSmoothOnBall (θ₀ ρ : ℝ) : normalLocation.IsSmoothOnBall θ₀ ρ :=
  fun x θ _ ↦ ⟨normalLocation_density_pos θ x, normalLocation_hasDerivAt_logLik x θ,
    normalLocation_hasDerivAt_score x θ⟩

/-- **The sample family of the normal location family satisfies every hypothesis** of the
asymptotic theory at every `θ₀`: it is regular, its score is smooth on the ball of radius `1`,
its log likelihood has derivative equal to its score there, and its information is `n`. Obtained
from `pi_regularity_of_isSmoothOnBall` with hypotheses on the normal family only. -/
theorem normalLocation_pi_regularity (n : ℕ) (θ₀ : ℝ) :
    (normalLocation.pi n).IsRegularAt θ₀ ∧ (normalLocation.pi n).IsScoreRegular θ₀ 1 ∧
      (∀ᵐ x ∂(normalLocation.pi n).law θ₀, ∀ θ ∈ closedBall θ₀ 1,
        HasDerivAt (fun u ↦ (normalLocation.pi n).logLik u x)
          ((normalLocation.pi n).score θ x) θ) ∧
      (normalLocation.pi n).fisherInfo θ₀ = n := by
  obtain ⟨h1, h2, h3, h4⟩ := pi_regularity_of_isSmoothOnBall n (normalLocation_isRegularAt θ₀)
    (normalLocation_isScoreRegular θ₀ one_pos) one_lt_two (normalLocation_isSmoothOnBall θ₀ 2)
  exact ⟨h1, h2, h3, by rw [h4, normalLocation_fisherInfo, mul_one]⟩

/-- The sample mean `(1/n) ∑ x_i` of `n` real observations. -/
noncomputable def realSampleMean (n : ℕ) (x : Fin n → ℝ) : ℝ :=
  (n : ℝ)⁻¹ * ∑ i, x i

lemma measurable_realSampleMean (n : ℕ) : Measurable (realSampleMean n) :=
  measurable_const.mul (Finset.measurable_sum _ fun i _ ↦ measurable_pi_apply i)

/-- On an i.i.d. `N(θ₀, 1)` sample the sample mean is asymptotically linear at `θ₀` with
influence function `x - θ₀`. -/
theorem realSampleMean_isAsymptoticallyLinear {θ₀ : ℝ} {O : ℕ → Ω → ℝ} (hO : IsIIDSample O μ)
    (hlaw : μ.map (O 0) = normalLocation.law θ₀) :
    IsAsymptoticallyLinear (fun n ω ↦ realSampleMean n fun i ↦ O i ω) θ₀
      (fun x ↦ x - θ₀) O μ := by
  have hlaw' : μ.map (O 0) = gaussianReal θ₀ 1 := hlaw.trans (normalLocation_law θ₀)
  have h2 : MemLp (fun ω ↦ id (O 0 ω)) 2 μ := by
    have h := memLp_id_gaussianReal' (μ := θ₀) (v := 1) 2 (by norm_num)
    rw [← hlaw'] at h
    exact (memLp_map_measure_iff aestronglyMeasurable_id (hO.aemeasurable 0)).1 h
  have hmean : μ[fun ω ↦ id (O 0 ω)] = θ₀ := by
    rw [integral_comp_eq_integral_law hO hlaw measurable_id, normalLocation_law]
    exact integral_id_gaussianReal
  have hAL := sampleMean_isAsymptoticallyLinear measurable_id h2
  rw [hmean] at hAL
  have hT : (fun n ω ↦ realSampleMean n fun i ↦ O i ω) = sampleMean id O := by
    funext n ω
    rw [realSampleMean, sampleMean, ← Fin.sum_univ_eq_sum_range (fun i ↦ id (O i ω))]
    rfl
  rw [hT]
  exact hAL

/-- In the normal location family the influence function `x - θ₀` has unit covariance with the
score and second moment `1`. -/
theorem normalLocation_integral_mul_score (θ₀ : ℝ) :
    ∫ x, (x - θ₀) * normalLocation.score θ₀ x ∂normalLocation.law θ₀ = 1 ∧
      ∫ x, (x - θ₀) ^ 2 ∂normalLocation.law θ₀ = 1 := by
  have h := normalLocation_fisherInfo θ₀
  rw [fisherInfo] at h
  simp_rw [normalLocation_score] at h ⊢
  simp_rw [← sq]
  exact ⟨h, h⟩

/-- **The sample mean is regular in the normal location family, by the covariance criterion**:
its influence function `x - θ₀` has `E[φ s] = 1`, so it is regular at every `θ₀` with limit
`N(0, E[φ²]) = N(0, 1)` (`isHajekRegular_of_integral_mul_score_eq_one`). -/
theorem realSampleMean_isHajekRegular (θ₀ : ℝ) :
    normalLocation.IsHajekRegular realSampleMean θ₀ (gaussianReal 0 1) := by
  have := isProbabilityMeasure_law (F := normalLocation) (θ := θ₀) (Set.mem_univ _)
  obtain ⟨Ω', _, P', O', hP', -, hO', hlaw'⟩ := exists_isIIDSample (normalLocation.law θ₀)
  have h := isHajekRegular_of_integral_mul_score_eq_one hO' (hlaw' 0).map_eq
    (normalLocation_isRegularAt θ₀) (normalLocation_isScoreRegular θ₀ one_pos)
    ((normalLocation_isSmoothOnBall θ₀ 2).ae_hasDerivAt_logLik one_lt_two)
    (by rw [normalLocation_fisherInfo]; exact one_pos) measurable_realSampleMean
    (realSampleMean_isAsymptoticallyLinear hO' (hlaw' 0).map_eq)
    (normalLocation_integral_mul_score θ₀).1
  rwa [(normalLocation_integral_mul_score θ₀).2, Real.toNNReal_one] at h

/-- **The sample mean attains the bound** in the normal location family: its limit variance
`E[φ²] = 1` equals the bound `I(θ₀)⁻¹`. Its influence function `x - θ₀` is the efficient one
`I(θ₀)⁻¹ s(θ₀; ·)`. -/
theorem realSampleMean_attains_bound (θ₀ : ℝ) :
    ∫ x, (x - θ₀) ^ 2 ∂normalLocation.law θ₀ = (normalLocation.fisherInfo θ₀)⁻¹ := by
  rw [(normalLocation_integral_mul_score θ₀).2, normalLocation_fisherInfo, inv_one]

end ParametricFamily

end CausalInference
