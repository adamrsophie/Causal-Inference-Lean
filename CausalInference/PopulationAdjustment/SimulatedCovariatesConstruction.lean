/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.BiasAnalysis.DistributionsExamples
public import CausalInference.Estimation.Estimator

/-!
# Simulated covariates by the normal to anything construction

When the target population reports only the margins of its covariates and their correlations,
standardization averages a fitted outcome surface over simulated covariates. The normal to
anything (NORTA) construction draws a Gaussian vector `Z ∼ N(0, R)` with a correlation matrix
`R` (unit diagonal) and sets `X_j = Q_j(Φ(Z_j))`, with `Φ` the standard normal distribution
function and `Q_j` the quantile function of the reported margin `μ_j`.

## Main definitions

* `nortaMap μ`: the map `z ↦ (Q_j(Φ(z_j)))_j`.
* `nortaLaw R μ`: the law of the simulated covariate vector, the image of `N(0, R)` under
  `nortaMap μ`.

## Main results

* `map_eval_nortaLaw`: every margin of the simulated law is the reported margin, exactly, for
  any correlation matrix and any margins (atoms allowed).
* `integral_nortaLaw_eval`, `integrable_nortaLaw_eval_iff`: integrals of functions of one
  coordinate.
* `charFun_map_pair_multivariateGaussian`, `map_pair_multivariateGaussian`: the pair
  `(Z_j, Z_k)` of `N(0, R)` has the standard bivariate normal law with correlation
  `R_{jk}`; `map_pair_nortaLaw`: the pair `(X_j, X_k)` of the simulated law is the image of
  that bivariate law under the two marginal transforms.
* `isIIDSample_nortaMap`: i.i.d. Gaussian draws give i.i.d. simulated covariates with the
  simulated law.
* `nortaMap_fairCoin`: for fair coin margins `X_j = 1{Z_j > 0}`.

## References

* M. C. Cario and B. L. Nelson (1997), *Modeling and generating random vectors with arbitrary
  marginal distributions and correlation matrix*, Northwestern University.
-/

@[expose] public section

namespace CausalInference

namespace PopulationAdjustment

open MeasureTheory ProbabilityTheory Set Matrix BiasAnalysis.Distributions

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **The normal to anything map**: `z ↦ (Q_j(Φ(z_j)))_j`, with `Φ` the standard normal
distribution function and `Q_j` the quantile function of the margin `μ_j`. -/
noncomputable def nortaMap (μ : ι → Measure ℝ) (z : EuclideanSpace ℝ ι) : ι → ℝ :=
  fun j => quantile (μ j) (cdf (gaussianReal 0 1) (z j))

/-- **The simulated covariate law**: the image of the centered Gaussian law `N(0, R)` under the
normal to anything map with margins `μ`. It is the intended law when `R` is a correlation
matrix (positive semidefinite with unit diagonal). -/
noncomputable def nortaLaw (R : Matrix ι ι ℝ) (μ : ι → Measure ℝ) : Measure (ι → ℝ) :=
  (multivariateGaussian 0 R).map (nortaMap μ)

omit [Fintype ι] [DecidableEq ι] in
theorem measurable_nortaMap_apply (μ : ι → Measure ℝ) (j : ι) :
    Measurable fun z : EuclideanSpace ℝ ι => nortaMap μ z j :=
  (measurable_quantile _).comp ((cdf (gaussianReal 0 1)).mono.measurable.comp (by fun_prop))

omit [Fintype ι] [DecidableEq ι] in
theorem measurable_nortaMap (μ : ι → Measure ℝ) : Measurable (nortaMap μ) :=
  Measurable.of_eval fun j => measurable_nortaMap_apply μ j

instance (R : Matrix ι ι ℝ) (μ : ι → Measure ℝ) : IsProbabilityMeasure (nortaLaw R μ) :=
  (Measure.isProbabilityMeasure_map_iff (measurable_nortaMap μ).aemeasurable).2 inferInstance

variable {R : Matrix ι ι ℝ} {μ : ι → Measure ℝ}

/-- A coordinate of `N(0, R)` with `R_{jj} = 1` is standard normal. -/
theorem hasLaw_eval_multivariateGaussian (hR : R.PosSemidef) {j : ι} (hj : R j j = 1) :
    HasLaw (fun z : EuclideanSpace ℝ ι => z j) (gaussianReal 0 1) (multivariateGaussian 0 R) := by
  have h := measurePreserving_eval_multivariateGaussian (μ := 0) hR (i := j)
  rw [hj] at h
  simpa using h.hasLaw

/-- **The margins of the simulated law are the reported margins.** For a positive semidefinite
`R` with unit diagonal and probability laws `μ_j` (with atoms or not), the `j`th coordinate of
the simulated covariate vector has law `μ_j`. -/
theorem map_eval_nortaLaw (hR : R.PosSemidef) (hdiag : ∀ i, R i i = 1)
    [∀ j, IsProbabilityMeasure (μ j)] (j : ι) :
    (nortaLaw R μ).map (fun x => x j) = μ j := by
  rw [nortaLaw, Measure.map_map (measurable_pi_apply j) (measurable_nortaMap μ)]
  exact (hasLaw_quantile_cdf_gaussian (hasLaw_eval_multivariateGaussian hR (hdiag j))
    (μ j)).map_eq

/-- Integrals of a function of one simulated coordinate are integrals against its margin. -/
theorem integral_nortaLaw_eval (hR : R.PosSemidef) (hdiag : ∀ i, R i i = 1)
    [∀ j, IsProbabilityMeasure (μ j)] (j : ι) {f : ℝ → ℝ} (hf : AEStronglyMeasurable f (μ j)) :
    ∫ x, f (x j) ∂nortaLaw R μ = ∫ t, f t ∂μ j := by
  rw [← map_eval_nortaLaw (μ := μ) hR hdiag j] at hf ⊢
  rw [integral_map (measurable_pi_apply j).aemeasurable hf]

/-- A function of one simulated coordinate is integrable exactly when it is integrable against
the margin. -/
theorem integrable_nortaLaw_eval_iff (hR : R.PosSemidef) (hdiag : ∀ i, R i i = 1)
    [∀ j, IsProbabilityMeasure (μ j)] (j : ι) {f : ℝ → ℝ} (hf : AEStronglyMeasurable f (μ j)) :
    Integrable (fun x => f (x j)) (nortaLaw R μ) ↔ Integrable f (μ j) := by
  rw [← map_eval_nortaLaw (μ := μ) hR hdiag j] at hf ⊢
  exact (integrable_map_measure hf (measurable_pi_apply j).aemeasurable).symm

/-! ### Pairs of coordinates -/

section Pair

omit [Fintype ι] [DecidableEq ι] in
/-- A correlation entry lies in `[-1, 1]`: `R_{jk}² ≤ 1`. -/
theorem sq_le_one_of_posSemidef [Finite ι] (hR : R.PosSemidef) (hdiag : ∀ i, R i i = 1) (j k : ι) :
    R j k ^ 2 ≤ 1 := by
  classical
  have := Fintype.ofFinite ι
  by_cases hjk : j = k
  · subst hjk; rw [hdiag]; norm_num
  have h := hR.dotProduct_mulVec_nonneg
    (fun i => (if i = j then R j k else 0) + if i = k then -1 else 0)
  have hsym : R k j = R j k := by simpa using congrFun (congrFun hR.1.eq j) k
  simp only [star_trivial, Matrix.mulVec, dotProduct, mul_add, add_mul, Finset.sum_add_distrib,
    mul_ite, ite_mul, mul_zero, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, ite_true] at h
  rw [hdiag, hdiag, hsym] at h
  nlinarith [h]

/-- The characteristic function of the pair `(Z_j, Z_k)` of `N(0, R)` with unit
diagonal: `t ↦ exp(-(t₀² + 2 R_{jk} t₀ t₁ + t₁²)/2)` when `R` is symmetric. -/
theorem charFun_map_pair_multivariateGaussian (hR : R.PosSemidef) (hdiag : ∀ i, R i i = 1)
    {j k : ι} (t : EuclideanSpace ℝ (Fin 2)) :
    charFun ((multivariateGaussian 0 R).map fun z => !₂[z j, z k]) t =
      Complex.exp (-((t 0 ^ 2 + 2 * R j k * t 0 * t 1 + t 1 ^ 2 : ℝ) : ℂ) / 2) := by
  have hm : Measurable fun z : EuclideanSpace ℝ ι => !₂[z j, z k] := by fun_prop
  set v : EuclideanSpace ℝ ι := EuclideanSpace.single j (t 0) + EuclideanSpace.single k (t 1)
  have hinner : ∀ z : EuclideanSpace ℝ ι, inner ℝ (!₂[z j, z k]) t = inner ℝ z v := fun z => by
    simp [v, PiLp.inner_apply, Fin.sum_univ_two, inner_add_right]
  rw [charFun_apply, integral_map hm.aemeasurable (by fun_prop)]
  simp_rw [hinner]
  rw [← charFun_apply, charFun_multivariateGaussian hR]
  have hsym : R k j = R j k := by simpa using congrFun (congrFun hR.1.eq j) k
  have hq : (v : ι → ℝ) ⬝ᵥ R *ᵥ (v : ι → ℝ) =
      t 0 ^ 2 + 2 * R j k * t 0 * t 1 + t 1 ^ 2 := by
    have hv : (v : ι → ℝ) = fun i => (if i = j then t 0 else 0) + if i = k then t 1 else 0 := by
      ext i; simp [v]
    simp only [hv, Matrix.mulVec, dotProduct, mul_add, add_mul, Finset.sum_add_distrib, mul_ite,
      ite_mul, mul_zero, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    rw [hdiag, hdiag, hsym]
    ring
  simp only [inner_zero_right, Complex.ofReal_zero, zero_mul, zero_sub, hq]
  push_cast
  ring_nf

/-- **The pair `(Z_j, Z_k)` of `N(0, R)` is standard bivariate normal with correlation
`R_{jk}`.** -/
theorem map_pair_multivariateGaussian (hR : R.PosSemidef) (hdiag : ∀ i, R i i = 1) {j k : ι} :
    (multivariateGaussian 0 R).map (fun z => !₂[z j, z k]) = bivariateNormal (R j k) := by
  have hρ := sq_le_one_of_posSemidef hR hdiag j k
  apply Measure.ext_of_charFun
  funext t
  rw [charFun_map_pair_multivariateGaussian hR hdiag, charFun_bivariateNormal hρ]


/-- **The pair law of the simulated covariates.** The pair `(X_j, X_k)` has the
law of `(Q_j(Φ(Z₀)), Q_k(Φ(Z₁)))` with `Z` standard bivariate normal with correlation
`R_{jk}`. -/
theorem map_pair_nortaLaw (hR : R.PosSemidef) (hdiag : ∀ i, R i i = 1) {j k : ι} :
    (nortaLaw R μ).map (fun x => (x j, x k)) =
      (bivariateNormal (R j k)).map (fun z => (quantile (μ j) (cdf (gaussianReal 0 1) (z 0)),
        quantile (μ k) (cdf (gaussianReal 0 1) (z 1)))) := by
  have hq : ∀ i : ι, Measurable fun t : ℝ => quantile (μ i) (cdf (gaussianReal 0 1) t) :=
    fun i => (measurable_quantile _).comp (cdf (gaussianReal 0 1)).mono.measurable
  rw [← map_pair_multivariateGaussian hR hdiag, nortaLaw,
    Measure.map_map (by fun_prop) (measurable_nortaMap μ),
    Measure.map_map (show Measurable fun z : EuclideanSpace ℝ (Fin 2) =>
      (quantile (μ j) (cdf (gaussianReal 0 1) (z 0)), quantile (μ k) (cdf (gaussianReal 0 1) (z 1)))
      from ((hq j).comp (by fun_prop)).prodMk ((hq k).comp (by fun_prop))) (by fun_prop)]
  rfl

end Pair

/-! ### Simulated draws -/

/-- **I.i.d. Gaussian draws give i.i.d. simulated covariates.** If `Z_0, Z_1, …` is an i.i.d.
sample with law `N(0, R)`, then `X_i = nortaMap μ (Z_i)` is an i.i.d. sample with law
`nortaLaw R μ`. -/
theorem isIIDSample_nortaMap {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {Z : ℕ → Ω → EuclideanSpace ℝ ι} (hZ : IsIIDSample Z P)
    (hZ0 : P.map (Z 0) = multivariateGaussian 0 R) :
    IsIIDSample (fun i ω => nortaMap μ (Z i ω)) P ∧
      P.map (fun ω => nortaMap μ (Z 0 ω)) = nortaLaw R μ := by
  refine ⟨hZ.comp (measurable_nortaMap μ), ?_⟩
  rw [nortaLaw, ← hZ0, AEMeasurable.map_map_of_aemeasurable
    (measurable_nortaMap μ).aemeasurable (hZ.aemeasurable 0)]
  rfl

/-! ### Fair coin margins -/

omit [Fintype ι] [DecidableEq ι] in
/-- For fair coin margins the simulated covariates are the signs of the Gaussian coordinates:
`X_j = 1{Z_j > 0}`. -/
theorem nortaMap_fairCoin (z : EuclideanSpace ℝ ι) (j : ι) :
    nortaMap (fun _ => fairCoin) z j = (Ioi (0 : ℝ)).indicator 1 (z j) :=
  quantile_fairCoin_cdf_stdNormal (z j)

end PopulationAdjustment

end CausalInference
