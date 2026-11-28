/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.MetaAnalysis.HierarchicalCredible
public import CausalInference.Estimation.PosteriorLimitQuantile
public import CausalInference.BiasAnalysis.DistributionsExamples

/-!
# The equal tailed credible interval of a posterior on the real line

For a posterior law `μ` on `ℝ` and `α ∈ (0, 1)`, the equal tailed interval
`[q(α/2), q(1 - α/2)]` of `PosteriorLimit.credibleInterval`, with the quantile
`q(p) = inf {x | p ≤ F(x)}`:

* is always a `(1 - α)` credible set in the sense of `IsCredibleSet`: its posterior probability
  is at least `1 - α` (`isCredibleSet_credibleInterval`). Proof: `F(q(1 - α/2)) ≥ 1 - α/2`, and
  `F(x) < α/2` for every `x < q(α/2)`, so the left limit of `F` at `q(α/2)` is at most `α/2`;
* has posterior probability exactly `1 - α` when the distribution function is continuous
  (`measure_credibleInterval_of_continuous`);
* can have probability larger than `1 - α` when the posterior has an atom: for the point mass at
  `0` and `α = 1/2` it is `{0}`, of probability `1` (`credibleInterval_dirac_zero`,
  `measure_credibleInterval_dirac_ne`);
* is the highest density interval `[m - √v z, m + √v z]` of a normal posterior `N(m, v)`,
  `v > 0`, with `Φ(z) = 1 - α/2` (`credibleInterval_gaussianReal_eq_hpdSet`); by
  `volume_le_of_gaussianReal_Icc` it is then the shortest set of its posterior probability.

## Main results

* `quantile_half_le`, `isCredibleSet_credibleInterval`, `measure_credibleInterval_of_continuous`,
  `credibleInterval_dirac_zero`, `measure_credibleInterval_dirac_ne`,
  `credibleInterval_gaussianReal_eq_hpdSet`.

## References

* A. Gelman, J. B. Carlin, H. S. Stern, D. B. Dunson, A. Vehtari and D. B. Rubin, *Bayesian Data
  Analysis*, third edition (2013).
-/

@[expose] public section

namespace CausalInference

namespace MetaAnalysis

open MeasureTheory ProbabilityTheory Set Filter Topology PosteriorLimit
open BiasAnalysis.Distributions
open scoped ENNReal NNReal

variable {μ : Measure ℝ} {α : ℝ}

/-- For `α ∈ (0, 1)` both levels `α/2` and `1 - α/2` lie in `(0, 1)`. -/
theorem half_mem_Ioo (hα0 : 0 < α) (hα1 : α < 1) :
    α / 2 ∈ Ioo (0 : ℝ) 1 ∧ 1 - α / 2 ∈ Ioo (0 : ℝ) 1 :=
  ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩

/-- The lower end of the equal tailed interval is at most the upper end. -/
theorem quantile_half_le (hα0 : 0 < α) (hα1 : α < 1) :
    quantile μ (α / 2) ≤ quantile μ (1 - α / 2) := by
  obtain ⟨hlo, hhi⟩ := half_mem_Ioo hα0 hα1
  rw [quantile_le_iff hlo]
  exact le_trans (by linarith) (le_cdf_quantile hhi)

/-- The left limit of the distribution function at the quantile `q(p)` is at most `p`. -/
theorem leftLim_cdf_quantile_le {p : ℝ} (hp : p ∈ Ioo (0 : ℝ) 1) :
    Function.leftLim (cdf μ) (quantile μ p) ≤ p := by
  have hlt : ∀ y < quantile μ p, cdf μ y ≤ p := fun y hy =>
    le_of_lt (not_le.1 fun h => absurd ((quantile_le_iff hp y).2 h) (not_le.2 hy))
  exact le_of_tendsto ((cdf μ).mono.tendsto_leftLim _)
    (eventually_nhdsWithin_of_forall fun y hy => hlt y hy)

/-- **The equal tailed interval is a `(1 - α)` credible set**: for a probability law `μ` on `ℝ`
and `α ∈ (0, 1)`, `μ([q(α/2), q(1 - α/2)]) ≥ 1 - α`. No continuity is needed. -/
theorem isCredibleSet_credibleInterval [IsProbabilityMeasure μ] (hα0 : 0 < α) (hα1 : α < 1) :
    IsCredibleSet μ α (credibleInterval μ α) := by
  obtain ⟨hlo, hhi⟩ := half_mem_Ioo hα0 hα1
  refine ⟨measurableSet_Icc, ?_⟩
  have hI := (cdf μ).measure_Icc (quantile μ (α / 2)) (quantile μ (1 - α / 2))
  rw [measure_cdf] at hI
  rw [credibleInterval, hI]
  refine ENNReal.ofReal_le_ofReal ?_
  have h1 := le_cdf_quantile (μ := μ) hhi
  have h2 := leftLim_cdf_quantile_le (μ := μ) hlo
  linarith

/-- **Exact level for a continuous distribution function**: if `F` is continuous, the equal
tailed interval has posterior probability exactly `1 - α`. -/
theorem measure_credibleInterval_of_continuous [IsProbabilityMeasure μ] (hα0 : 0 < α)
    (hα1 : α < 1) (hF : Continuous (cdf μ)) :
    μ (credibleInterval μ α) = ENNReal.ofReal (1 - α) := by
  obtain ⟨hlo, hhi⟩ := half_mem_Ioo hα0 hα1
  have hleft : Function.leftLim (cdf μ) (quantile μ (α / 2)) = cdf μ (quantile μ (α / 2)) :=
    tendsto_nhds_unique ((cdf μ).mono.tendsto_leftLim _)
      ((hF.tendsto _).mono_left nhdsWithin_le_nhds)
  have hI := (cdf μ).measure_Icc (quantile μ (α / 2)) (quantile μ (1 - α / 2))
  rw [measure_cdf] at hI
  rw [credibleInterval, hI, hleft, cdf_quantile hhi hF, cdf_quantile hlo hF]
  congr 1
  ring

/-- The quantiles of the point mass at `0` are `0`. -/
theorem quantile_dirac_zero {u : ℝ} (hu : u ∈ Ioo (0 : ℝ) 1) :
    quantile (Measure.dirac (0 : ℝ)) u = 0 := by
  have hF : ∀ x, u ≤ cdf (Measure.dirac (0 : ℝ)) x ↔ 0 ≤ x := by
    intro x
    rw [cdf_eq_real]
    by_cases hx : 0 ≤ x
    · simp only [hx, iff_true]
      rw [measureReal_def, Measure.dirac_apply_of_mem (Set.mem_Iic.2 hx), ENNReal.toReal_one]
      exact hu.2.le
    · simp only [hx, iff_false, not_le]
      rw [measureReal_def, Measure.dirac_apply' _ measurableSet_Iic,
        Set.indicator_of_notMem (by simpa using hx), ENNReal.toReal_zero]
      exact hu.1
  refine le_antisymm ((quantile_le_iff hu 0).2 ((hF 0).2 le_rfl)) ?_
  exact (hF _).1 ((quantile_le_iff hu _).1 le_rfl)

/-- **With an atom the level is not exact**: for the point mass at `0` and `α = 1/2` the equal
tailed interval is `{0}`. -/
theorem credibleInterval_dirac_zero : credibleInterval (Measure.dirac (0 : ℝ)) (1 / 2) = {0} := by
  rw [credibleInterval, quantile_dirac_zero ⟨by norm_num, by norm_num⟩,
    quantile_dirac_zero ⟨by norm_num, by norm_num⟩, Icc_self]

/-- **The atom counterexample**: the equal tailed interval of the point mass at `0` at level
`1 - 1/2` has probability `1`, not `1/2`. -/
theorem measure_credibleInterval_dirac_ne :
    Measure.dirac (0 : ℝ) (credibleInterval (Measure.dirac (0 : ℝ)) (1 / 2)) = 1 ∧
      Measure.dirac (0 : ℝ) (credibleInterval (Measure.dirac (0 : ℝ)) (1 / 2)) ≠
        ENNReal.ofReal (1 - 1 / 2) := by
  rw [credibleInterval_dirac_zero, Measure.dirac_apply_of_mem (Set.mem_singleton 0)]
  refine ⟨rfl, ?_⟩
  rw [Ne, eq_comm, ENNReal.ofReal_eq_one]
  norm_num

/-- `Φ(0) = 1/2` for the standard normal distribution function. -/
theorem cdf_stdNormal_zero : cdf (gaussianReal 0 1) 0 = 1 / 2 := by
  have h := cdf_stdNormal_neg 0
  rw [neg_zero] at h
  linarith

/-- **For a normal posterior the equal tailed interval is the highest density interval**: for
`N(m, v)`, `v > 0`, `α < 1` and `Φ(z) = 1 - α/2`, the equal tailed interval is
`[m - √v z, m + √v z]`, the highest density set `{x | φ(m + √v z) ≤ φ(x)}`. -/
theorem credibleInterval_gaussianReal_eq_hpdSet (m : ℝ) {v : ℝ≥0} (hv : v ≠ 0) (hα1 : α < 1)
    {z : ℝ} (hzα : cdf (gaussianReal 0 1) z = 1 - α / 2) :
    credibleInterval (gaussianReal m v) α = Icc (m - √v * z) (m + √v * z) ∧
      credibleInterval (gaussianReal m v) α =
        hpdSet (gaussianPDF m v) (gaussianPDF m v (m + √v * z)) := by
  have hs : 0 < √(v : ℝ) := Real.sqrt_pos.2 (by positivity)
  have hvv : (v : ℝ) = √(v : ℝ) ^ 2 := (Real.sq_sqrt v.coe_nonneg).symm
  have hac := gaussianReal_absolutelyContinuous' m hv
  have hz0 : 0 ≤ z := by
    by_contra h
    have := (cdf (gaussianReal 0 1)).mono (not_le.1 h).le
    rw [hzα, cdf_stdNormal_zero] at this
    linarith
  have hup : quantile (gaussianReal m v) (1 - α / 2) = m + √v * z := by
    rw [← hzα, ← cdf_gaussianReal_affine m hs hvv z, quantile_cdf_of_absolutelyContinuous hac]
  have hlow : quantile (gaussianReal m v) (α / 2) = m - √v * z := by
    have h : α / 2 = cdf (gaussianReal 0 1) (-z) := by rw [cdf_stdNormal_neg, hzα]; ring
    rw [h, ← cdf_gaussianReal_affine m hs hvv (-z), quantile_cdf_of_absolutelyContinuous hac]
    ring
  have hI : credibleInterval (gaussianReal m v) α = Icc (m - √v * z) (m + √v * z) := by
    rw [credibleInterval, hup, hlow]
  refine ⟨hI, ?_⟩
  rw [hI, hpdSet_gaussianPDF m hv (mul_nonneg hs.le hz0)]

end MetaAnalysis

end CausalInference
