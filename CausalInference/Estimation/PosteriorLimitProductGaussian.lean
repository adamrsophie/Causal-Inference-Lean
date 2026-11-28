/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.Estimation.PosteriorLimitLaplaceGaussian
public import CausalInference.MetaAnalysis.ConjugateMultivariateNormal

/-!
# The two forms of the multivariate normal density agree

The library writes the density of `N(m, S)` on `EuclideanSpace ℝ ι` in two ways: with the
quadratic form `quadForm S⁻¹ (x - m)` (`PosteriorLimit.mvGaussianPDF`) and with the explicit
product `(x - m)ᵀ S⁻¹ (x - m)` of coordinate vectors (`MetaAnalysis.multivariateGaussianPDF`).
They are the same function for every `m` and every matrix `S`
(`mvGaussianPDF_eq_multivariateGaussianPDF`).

## Main results

* `mvGaussianPDF_eq_multivariateGaussianPDF`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Matrix

namespace CausalInference

namespace PosteriorLimit

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **The two forms of the multivariate normal density agree**: for every center `m`, matrix
`S` and point `x`, `mvGaussianPDF m S x = multivariateGaussianPDF m S x`. -/
theorem mvGaussianPDF_eq_multivariateGaussianPDF (m : EuclideanSpace ℝ ι) (S : Matrix ι ι ℝ)
    (x : EuclideanSpace ℝ ι) :
    mvGaussianPDF m S x = MetaAnalysis.multivariateGaussianPDF m S x := by
  rw [mvGaussianPDF, MetaAnalysis.multivariateGaussianPDF, quadForm, WithLp.ofLp_sub]

end PosteriorLimit

end CausalInference
