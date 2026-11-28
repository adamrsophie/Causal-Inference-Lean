/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.Estimation.HajekConvolutionGeneral
public import CausalInference.Estimation.HajekRegularLinearVector

/-!
# The Hájek convolution bound for a general limit law, vector parameter and functionals

The vector and functional forms of
`CausalInference.ParametricFamily.hajek_convolution_bound_general`. For a regular estimator of a
real functional `ψ` with gradient `g` at `θ₀` and an arbitrary limit law `L` of finite second
moment, `Var(L) ≥ gᵀ I(θ₀)⁻¹ g`; for a regular estimator of the vector
parameter with a limit law `L` of finite second moment on `ℝ^p`, the covariance matrix of `L`
minus `I(θ₀)⁻¹` is positive semidefinite. The reductions are those of the Gaussian case: a
functional is reduced to the scalar bound along the line through `θ₀` in the direction
`I(θ₀)⁻¹ g` (`IsHajekRegularFunctional.isHajekRegular_line`), and the vector parameter to the
functionals `θ ↦ aᵀ θ` (`IsHajekRegularVec.dotProduct`), the variance of `⟪y, a⟫` under `L`
being the quadratic form `aᵀ Σ_L a` of the covariance matrix.

The last section links the cross moment `crossMoment μ φ φ = E_μ[φ φᵀ]` with the covariance
matrix `covMatrix` when `φ` has mean zero, and restates the decomposition
`Σ = I(θ₀)⁻¹ + Cov(φ - I(θ₀)⁻¹ s)` of an influence function with unit cross moment with the
score in terms of covariance matrices.

## Main results

* `CausalInference.ParametricFamily.IsHajekRegularFunctional.isProbabilityMeasure`: the limit
  law of a regular estimator of a functional is a probability measure.
* `CausalInference.ParametricFamily.hajek_convolution_bound_functional_general`:
  `gᵀ I(θ₀)⁻¹ g ≤ Var(L)`.
* `CausalInference.ParametricFamily.hajek_convolution_bound_vec_general`:
  `Σ_L - I(θ₀)⁻¹` is positive semidefinite, `Σ_L` the covariance matrix of `L`.
* `CausalInference.crossMoment_self_eq_covMatrix`: `E_μ[φ φᵀ] = Cov_μ(φ)` for `φ` of mean zero.
* `CausalInference.ParametricFamily.covMatrix_eq_inv_add`,
  `CausalInference.ParametricFamily.covMatrix_eq_inv_iff`: `Cov(φ) = I(θ₀)⁻¹ + Cov(φ - I⁻¹ s)`,
  so `Cov(φ) - I(θ₀)⁻¹` is positive semidefinite, with equality exactly when `φ = I(θ₀)⁻¹ s`.

References: J. Hájek (1970), *A characterization of limiting distributions of regular
estimates*, Zeitschrift für Wahrscheinlichkeitstheorie und verwandte Gebiete; A. W. van der
Vaart (1998), *Asymptotic Statistics*, chapter 8.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Finset Metric Matrix
open scoped Topology ENNReal NNReal BoundedContinuousFunction RealInnerProductSpace

namespace CausalInference

open BiasAnalysis.MeasurementError (covMatrix)

namespace ParametricFamily

variable {S : Type*} [MeasurableSpace S] {p : ℕ} {F : ParametricFamily (Fin p → ℝ) S}
  [SigmaFinite F.ν] {θ₀ : Fin p → ℝ}

/-- **The limit law of a regular estimator of a functional is a probability measure.** At
`θ₀ ∈ Θ` the sample laws at local parameter `0` are probability measures and the constant `1` is
a test function. -/
theorem IsHajekRegularFunctional.isProbabilityMeasure (hθ₀ : θ₀ ∈ F.Θ)
    {T : ∀ n, (Fin n → S) → ℝ} {ψ : (Fin p → ℝ) → ℝ} {L : Measure ℝ}
    (hT : F.IsHajekRegularFunctional T ψ θ₀ L) : IsProbabilityMeasure L := by
  have h1 := hT.tendsto 0 (BoundedContinuousFunction.const _ 1)
  simp only [BoundedContinuousFunction.const_apply, integral_const, smul_eq_mul, mul_one,
    smul_zero, add_zero] at h1
  refine isProbabilityMeasure_iff_real.2 (tendsto_nhds_unique h1 (tendsto_const_nhds.congr ?_))
  intro n
  have := isProbabilityMeasure_law (F := F.pi n) hθ₀
  exact probReal_univ.symm

/-- **The Hájek convolution bound for a functional, general limit law.** In a family regular at
`θ₀` (`IsRegularAtVec`), with score regular on a closed ball (`IsScoreRegularVec`) and positive
definite information `I(θ₀)`, let `ψ` have gradient `g` at `θ₀` and let the line through `θ₀` in
the direction `I(θ₀)⁻¹ g` be measurable (`LineMeasurable`). Every estimator of `ψ` regular at
`θ₀` whose limit law `L` has a finite second moment has `gᵀ I(θ₀)⁻¹ g ≤ Var(L)`. For `g ≠ 0`, in
the line through `θ₀` in the direction `v = I⁻¹ g`, with information `c = gᵀ I⁻¹ g`, the statistic
`(T_n - ψ(θ₀)) / c` is regular with limit the image of `L` under `y ↦ y / c`, of variance
`Var(L) / c²`; the scalar bound gives `c⁻¹ ≤ Var(L) / c²`. -/
theorem hajek_convolution_bound_functional_general (hreg : F.IsRegularAtVec θ₀) {r : ℝ}
    (hs : F.IsScoreRegularVec θ₀ r) (hI : (F.fisherInfoMatrix θ₀).PosDef)
    {ψ : (Fin p → ℝ) → ℝ} {g : Fin p → ℝ} (hψ : HasFDerivAt ψ (gradCLM g) θ₀)
    (hm : F.LineMeasurable θ₀ ((F.fisherInfoMatrix θ₀)⁻¹ *ᵥ g))
    {T : ∀ n, (Fin n → S) → ℝ} {L : Measure ℝ}
    (hT : F.IsHajekRegularFunctional T ψ θ₀ L) (hL : MemLp id 2 L) :
    g ⬝ᵥ ((F.fisherInfoMatrix θ₀)⁻¹ *ᵥ g) ≤ Var[id; L] := by
  by_cases hg : g = 0
  · simp [hg]
  obtain ⟨ε, hε, hball, -⟩ := hreg.exists_ball_pos
  have hΘ : F.Θ ∈ 𝓝 θ₀ := Filter.mem_of_superset (ball_mem_nhds θ₀ hε) hball
  have := hT.isProbabilityMeasure (mem_of_mem_nhds hΘ)
  set v := (F.fisherInfoMatrix θ₀)⁻¹ *ᵥ g with hvdef
  set c := g ⬝ᵥ v with hcdef
  have hc : 0 < c := by simpa using hI.inv.dotProduct_mulVec_pos hg
  have hv : v ≠ 0 := fun h0 ↦ by rw [hcdef, h0, dotProduct_zero] at hc; exact lt_irrefl _ hc
  have hψv : gradCLM g v ≠ 0 := by rw [gradCLM_apply]; exact hc.ne'
  obtain ⟨hR, hIpos, r', -, hsr, hdl⟩ := line_hypotheses hreg hs hI hv hm
  have hTl := hT.isHajekRegular_line hΘ hψ hψv
  have hdiv : (fun y : ℝ ↦ y / gradCLM g v) = (c⁻¹ * ·) := by
    funext y
    rw [gradCLM_apply, div_eq_inv_mul]
  rw [hdiv] at hTl
  have hmeas : Measurable (c⁻¹ * · : ℝ → ℝ) := measurable_const_mul _
  have hL' : MemLp id 2 (L.map (c⁻¹ * ·)) :=
    (memLp_map_measure_iff aestronglyMeasurable_id hmeas.aemeasurable).2 (hL.const_mul c⁻¹)
  have hb := hajek_convolution_bound_general hR hsr hdl hIpos hTl hL'
  have hvar : Var[id; L.map (c⁻¹ * ·)] = c⁻¹ ^ 2 * Var[id; L] := by
    rw [variance_map aemeasurable_id hmeas.aemeasurable]
    exact variance_const_mul c⁻¹ id L
  have hq : v ⬝ᵥ (F.fisherInfoMatrix θ₀ *ᵥ v) = c := by
    rw [hvdef, mulVec_inv_mulVec hI, dotProduct_comm]
  rw [hvar, line_fisherInfo hreg v, hq] at hb
  calc c = c ^ 2 * c⁻¹ := by field_simp
    _ ≤ c ^ 2 * (c⁻¹ ^ 2 * Var[id; L]) := mul_le_mul_of_nonneg_left hb (sq_nonneg c)
    _ = Var[id; L] := by field_simp

/-- **The Hájek convolution bound, vector parameter, general limit law.** In a family regular
at `θ₀` (`IsRegularAtVec`), with score regular on a closed ball (`IsScoreRegularVec`), positive
definite information `I(θ₀)` and measurable lines through `θ₀` in the directions `I(θ₀)⁻¹ a`,
every estimator regular at `θ₀` whose limit law `L` on `ℝ^p` has a finite second moment satisfies
`aᵀ I(θ₀)⁻¹ a ≤ aᵀ Σ_L a` for every `a`, where `Σ_L` is the covariance matrix of the coordinates
under `L`; that is, `Σ_L - I(θ₀)⁻¹` is positive semidefinite. -/
theorem hajek_convolution_bound_vec_general (hreg : F.IsRegularAtVec θ₀) {r : ℝ}
    (hs : F.IsScoreRegularVec θ₀ r) (hI : (F.fisherInfoMatrix θ₀).PosDef)
    (hm : ∀ a, F.LineMeasurable θ₀ ((F.fisherInfoMatrix θ₀)⁻¹ *ᵥ a))
    {T : ∀ n, (Fin n → S) → Fin p → ℝ} {L : Measure (EuclideanSpace ℝ (Fin p))}
    (hT : F.IsHajekRegularVec T θ₀ L) (hL : MemLp id 2 L) :
    (∀ a : Fin p → ℝ, a ⬝ᵥ ((F.fisherInfoMatrix θ₀)⁻¹ *ᵥ a) ≤
        a ⬝ᵥ (covMatrix L (fun i y ↦ y i) *ᵥ a)) ∧
      (covMatrix L (fun i y ↦ y i) - (F.fisherInfoMatrix θ₀)⁻¹).PosSemidef := by
  obtain ⟨ε, hε, hball, -⟩ := hreg.exists_ball_pos
  have hΘ : F.Θ ∈ 𝓝 θ₀ := Filter.mem_of_superset (ball_mem_nhds θ₀ hε) hball
  have := hT.isProbabilityMeasure hΘ
  have hquad : ∀ a : Fin p → ℝ, a ⬝ᵥ ((F.fisherInfoMatrix θ₀)⁻¹ *ᵥ a) ≤
      a ⬝ᵥ (covMatrix L (fun i y ↦ y i) *ᵥ a) := by
    intro a
    have ha := hT.dotProduct a
    have hci : Continuous fun y : EuclideanSpace ℝ (Fin p) ↦ ⟪y, WithLp.toLp 2 a⟫ :=
      continuous_id.inner continuous_const
    have hfun : (fun y : EuclideanSpace ℝ (Fin p) ↦ ⟪y, WithLp.toLp 2 a⟫) =
        fun y ↦ innerSL ℝ (WithLp.toLp 2 a) y := by
      funext y
      rw [innerSL_apply_apply, real_inner_comm]
    have hmem : MemLp (fun y : EuclideanSpace ℝ (Fin p) ↦ ⟪y, WithLp.toLp 2 a⟫) 2 L := by
      rw [hfun]
      exact (innerSL ℝ (WithLp.toLp 2 a)).comp_memLp' hL
    have hL' : MemLp id 2 (L.map fun y ↦ ⟪y, WithLp.toLp 2 a⟫) :=
      (memLp_map_measure_iff aestronglyMeasurable_id hci.aemeasurable).2 hmem
    have hb := hajek_convolution_bound_functional_general hreg hs hI
      (by simpa [← gradCLM_apply] using (gradCLM a).hasFDerivAt) (hm a) ha hL'
    rw [variance_map aemeasurable_id hci.aemeasurable] at hb
    have hv := variance_inner_eq_covMatrix (μ := L) (V := id) hL (WithLp.toLp 2 a)
    simp only [id] at hv
    rw [Function.id_comp, hv] at hb
    exact hb
  have hcoord : ∀ i, MemLp (fun y : EuclideanSpace ℝ (Fin p) ↦ y i) 2 L := fun i ↦
    (EuclideanSpace.proj (𝕜 := ℝ) i).comp_memLp' hL
  refine ⟨hquad, posSemidef_iff_dotProduct_mulVec.2
    ⟨(posSemidef_covMatrix hcoord).isHermitian.sub hI.isHermitian.inv, fun a ↦ ?_⟩⟩
  rw [star_trivial, sub_mulVec, dotProduct_sub, sub_nonneg]
  exact hquad a

end ParametricFamily

/-! ### Cross moments and covariance matrices -/

section CovMatrix

variable {S : Type*} [MeasurableSpace S] {p : ℕ}

/-- **The second moment of a centered vector is its covariance matrix.** If every coordinate of
`φ` has mean zero under `μ`, then `E_μ[φ φᵀ] = Cov_μ(φ)`. No integrability hypothesis is needed:
with the means equal to zero the two matrices have the same integrands entry by entry. -/
theorem crossMoment_self_eq_covMatrix {μ : Measure S} {φ : S → Fin p → ℝ}
    (h0 : ∀ j, ∫ x, φ x j ∂μ = 0) :
    crossMoment μ φ φ = covMatrix μ (fun j x ↦ φ x j) := by
  ext j k
  simp only [crossMoment, covMatrix, Matrix.of_apply, covariance, h0, sub_zero]

namespace ParametricFamily

variable {F : ParametricFamily (Fin p → ℝ) S} {θ₀ : Fin p → ℝ}

/-- The efficient influence function `I(θ₀)⁻¹ s(θ₀; ·)` has mean zero at a regular point. -/
theorem integral_inv_mulVec_scoreVec (hreg : F.IsRegularAtVec θ₀) (j : Fin p) :
    ∫ x, ((F.fisherInfoMatrix θ₀)⁻¹ *ᵥ F.scoreVec θ₀ x) j ∂F.law θ₀ = 0 := by
  have := isProbabilityMeasure_law (mem_of_mem_nhds hreg.mem_nhds)
  have hint : ∀ k, Integrable (fun x ↦ F.scoreVec θ₀ x k) (F.law θ₀) := fun k ↦
    (hreg.memLp_scoreVec k).integrable one_le_two
  simp only [mulVec, dotProduct]
  rw [integral_finsetSum _ fun k _ ↦ (hint k).const_mul _]
  refine Finset.sum_eq_zero fun k _ ↦ ?_
  rw [integral_const_mul,
    integral_scoreVec_eq_zero hreg.mem_nhds hreg.interchange.1.self_of_nhds k, mul_zero]

/-- **The covariance decomposition of an influence function with unit cross moment.** At a
regular point with positive definite information, let `φ` be square integrable under `P_θ₀` with
mean zero and `E_θ₀[φ sᵀ] = 1`. Then
`Cov(φ) = I(θ₀)⁻¹ + Cov(φ - I(θ₀)⁻¹ s)`. This is `crossMoment_eq_inv_add` for covariance
matrices; the mean zero hypothesis identifies the second moments with covariances. -/
theorem covMatrix_eq_inv_add (hreg : F.IsRegularAtVec θ₀)
    (hI : (F.fisherInfoMatrix θ₀).PosDef) {φ : S → Fin p → ℝ}
    (hφ : ∀ j, MemLp (fun x ↦ φ x j) 2 (F.law θ₀)) (h0 : ∀ j, ∫ x, φ x j ∂F.law θ₀ = 0)
    (hc : crossMoment (F.law θ₀) φ (F.scoreVec θ₀) = 1) :
    covMatrix (F.law θ₀) (fun j x ↦ φ x j) = (F.fisherInfoMatrix θ₀)⁻¹ +
      covMatrix (F.law θ₀)
        (fun j x ↦ (φ x - (F.fisherInfoMatrix θ₀)⁻¹ *ᵥ F.scoreVec θ₀ x) j) := by
  have := isProbabilityMeasure_law (mem_of_mem_nhds hreg.mem_nhds)
  have h0' : ∀ j, ∫ x, (φ x - (F.fisherInfoMatrix θ₀)⁻¹ *ᵥ F.scoreVec θ₀ x) j ∂F.law θ₀ = 0 := by
    intro j
    have hs : Integrable (fun x ↦ ((F.fisherInfoMatrix θ₀)⁻¹ *ᵥ F.scoreVec θ₀ x) j)
        (F.law θ₀) := (memLp_dotProduct hreg.memLp_scoreVec
      fun k ↦ (F.fisherInfoMatrix θ₀)⁻¹ j k).integrable one_le_two
    simp only [Pi.sub_apply]
    rw [integral_sub ((hφ j).integrable one_le_two) hs, h0 j]
    have := integral_inv_mulVec_scoreVec hreg j
    simp only [mulVec] at this ⊢
    rw [this, sub_zero]
  rw [← crossMoment_self_eq_covMatrix h0, ← crossMoment_self_eq_covMatrix h0']
  exact crossMoment_eq_inv_add hreg hI hφ hc

/-- **The covariance bound for an influence function with unit cross moment.** Under the
hypotheses of `covMatrix_eq_inv_add`, `Cov(φ) - I(θ₀)⁻¹` is positive semidefinite, and
`Cov(φ) = I(θ₀)⁻¹` exactly when `φ = I(θ₀)⁻¹ s(θ₀; ·)` almost everywhere under `P_θ₀`. This is
`crossMoment_eq_inv_iff` for covariance matrices. -/
theorem covMatrix_eq_inv_iff (hreg : F.IsRegularAtVec θ₀)
    (hI : (F.fisherInfoMatrix θ₀).PosDef) {φ : S → Fin p → ℝ}
    (hφ : ∀ j, MemLp (fun x ↦ φ x j) 2 (F.law θ₀)) (h0 : ∀ j, ∫ x, φ x j ∂F.law θ₀ = 0)
    (hc : crossMoment (F.law θ₀) φ (F.scoreVec θ₀) = 1) :
    (covMatrix (F.law θ₀) (fun j x ↦ φ x j) - (F.fisherInfoMatrix θ₀)⁻¹).PosSemidef ∧
      (covMatrix (F.law θ₀) (fun j x ↦ φ x j) = (F.fisherInfoMatrix θ₀)⁻¹ ↔
        φ =ᵐ[F.law θ₀] fun x ↦ (F.fisherInfoMatrix θ₀)⁻¹ *ᵥ F.scoreVec θ₀ x) := by
  rw [← crossMoment_self_eq_covMatrix h0]
  exact crossMoment_eq_inv_iff hreg hI hφ hc

end ParametricFamily

end CovMatrix

end CausalInference
