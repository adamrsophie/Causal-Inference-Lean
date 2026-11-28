/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.Estimation.FisherInformation
public import Mathlib.Analysis.Calculus.FDeriv.Pi
public import Mathlib.Analysis.Calculus.ContDiff.Operations

/-!
# Score vector and Fisher information matrix

For a family `F : ParametricFamily (Fin p → ℝ) S` with a vector parameter `θ ∈ ℝ^p`, the score
vector has components `s_j(θ;x) = ∂_j f(x;θ) / f(x;θ)`, partial derivatives being derivatives
along coordinate lines, and the Fisher information matrix is `I(θ)_{jk} = E_θ[s_j s_k]`. Each
coordinate line through `θ` is a scalar family (`ParametricFamily.slice`), so the mean zero
property of the score and the derivative of the mean of a statistic come from the scalar case.

## Main definitions

* `CausalInference.ParametricFamily.slice`: the scalar family along the `j`-th coordinate line.
* `CausalInference.ParametricFamily.partialDeriv`, `partialDeriv2`, `scoreVec`,
  `partialLogLik`, `hessianLogLik`, `fisherInfoMatrix`, `gradMean`.
* `CausalInference.ParametricFamily.PartialDerivInterchange`, `PartialDerivInterchangeTwo`,
  `MeanPartialDerivInterchange`: interchange of partial derivatives and integrals, including
  the integrability of the differentiated integrands.
* `CausalInference.ParametricFamily.IsRegularAtVec`: a regular point, with envelope conditions.

## Main results

* `CausalInference.ParametricFamily.integral_scoreVec_eq_zero`: `E_θ[s_j] = 0`.
* `CausalInference.ParametricFamily.fisherInfoMatrix_eq_covariance`: `I(θ) = Cov_θ(s)`.
* `CausalInference.ParametricFamily.gradMean_eq`: `∂_j E_θ[T] = E_θ[T s_j]`.
* `CausalInference.ParametricFamily.sum_scoreVec_covariance_of_isIIDSample`: for an i.i.d.
  sample of size `n`, the sample score has covariance matrix `n I(θ)`.
* `CausalInference.ParametricFamily.information_equality_vec`: `I(θ)_{jk} = -E_θ[∂_j ∂_k ℓ]`.
* `CausalInference.ParametricFamily.interchange_of_dominated`: the interchanges from integrable
  envelopes of the first and second partial derivatives.

References: E. L. Lehmann and G. Casella (1998), *Theory of Point Estimation*, 2nd edition,
chapter 2.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology Metric Matrix
open scoped ENNReal

namespace CausalInference

namespace ParametricFamily

variable {S : Type*} [MeasurableSpace S] {p : ℕ} (F : ParametricFamily (Fin p → ℝ) S)

/-- The scalar family along the `j`-th coordinate line through `θ`: `t ↦ f(·; θ with θ_j := t)`,
with parameter set `{t | θ with θ_j := t ∈ Θ}`. -/
noncomputable def slice (θ : Fin p → ℝ) (j : Fin p) : ParametricFamily ℝ S where
  ν := F.ν
  Θ := {t | Function.update θ j t ∈ F.Θ}
  density t x := F.density (Function.update θ j t) x
  measurable_density _ := F.measurable_density _
  density_nonneg _ ht x := F.density_nonneg _ ht x
  integrable_density _ ht := F.integrable_density _ ht
  integral_density _ ht := F.integral_density _ ht

/-- The partial derivative `∂f(x;θ)/∂θ_j`. -/
noncomputable def partialDeriv (j : Fin p) (θ : Fin p → ℝ) (x : S) : ℝ :=
  deriv (fun t ↦ F.density (Function.update θ j t) x) (θ j)

/-- The second partial derivative `∂²f(x;θ)/∂θ_j∂θ_k` (first `∂_k`, then `∂_j`). -/
noncomputable def partialDeriv2 (j k : Fin p) (θ : Fin p → ℝ) (x : S) : ℝ :=
  deriv (fun t ↦ F.partialDeriv k (Function.update θ j t) x) (θ j)

/-- The score vector `s(θ;x)_j = ∂_j f(x;θ) / f(x;θ)` (`0` where the density vanishes, a
`P_θ`-null set). -/
noncomputable def scoreVec (θ : Fin p → ℝ) (x : S) : Fin p → ℝ :=
  fun j ↦ F.partialDeriv j θ x / F.density θ x

/-- The partial derivative `∂ℓ(θ;x)/∂θ_k` of the log-likelihood. -/
noncomputable def partialLogLik (k : Fin p) (θ : Fin p → ℝ) (x : S) : ℝ :=
  deriv (fun t ↦ Real.log (F.density (Function.update θ k t) x)) (θ k)

/-- The entry `∂²ℓ(θ;x)/∂θ_j∂θ_k` of the Hessian of the log-likelihood. -/
noncomputable def hessianLogLik (j k : Fin p) (θ : Fin p → ℝ) (x : S) : ℝ :=
  deriv (fun t ↦ F.partialLogLik k (Function.update θ j t) x) (θ j)

/-- The Fisher information matrix `I(θ)_{jk} = E_θ[s_j(θ;X) s_k(θ;X)]`. -/
noncomputable def fisherInfoMatrix (θ : Fin p → ℝ) : Matrix (Fin p) (Fin p) ℝ :=
  Matrix.of fun j k ↦ ∫ x, F.scoreVec θ x j * F.scoreVec θ x k ∂F.law θ

/-- The gradient of the mean `g(θ) = E_θ[T]`: the vector of its partial derivatives. -/
noncomputable def gradMean (T : S → ℝ) (θ : Fin p → ℝ) : Fin p → ℝ :=
  fun j ↦ deriv (fun t ↦ F.mean T (Function.update θ j t)) (θ j)

/-- First order interchange at `θ`: along every coordinate line, `∂_j f(·;θ)` is integrable and
the partial derivative of `∫ f dν` is `∫ ∂_j f dν`. -/
def PartialDerivInterchange (θ : Fin p → ℝ) : Prop :=
  ∀ j, (F.slice θ j).DerivInterchange (θ j)

/-- Interchange for the mean of a statistic `T` at `θ`, along every coordinate line. -/
def MeanPartialDerivInterchange (T : S → ℝ) (θ : Fin p → ℝ) : Prop :=
  ∀ j, (F.slice θ j).MeanDerivInterchange T (θ j)

/-- Second order interchange at `θ`: every `∂_j ∂_k f(·;θ)` is integrable and the partial
derivative in `θ_j` of `∫ ∂_k f dν` is `∫ ∂_j ∂_k f dν`. -/
def PartialDerivInterchangeTwo (θ : Fin p → ℝ) : Prop :=
  ∀ j k, Integrable (F.partialDeriv2 j k θ) F.ν ∧
    HasDerivAt (fun t ↦ ∫ x, F.partialDeriv k (Function.update θ j t) x ∂F.ν)
      (∫ x, F.partialDeriv2 j k θ x ∂F.ν) (θ j)

variable {F}

/-- At its base point the coordinate slice has the law `P_θ`. -/
theorem slice_law_self (θ : Fin p → ℝ) (j : Fin p) : (F.slice θ j).law (θ j) = F.law θ := by
  simp [law, slice]

/-- At its base point the score of the `j`-th slice is the `j`-th component of the score
vector. -/
theorem slice_score_self (θ : Fin p → ℝ) (j : Fin p) :
    (F.slice θ j).score (θ j) = fun x ↦ F.scoreVec θ x j := by
  ext x
  simp [score, densityDeriv, scoreVec, partialDeriv, slice]

/-- At its base point the density derivative of the `j`-th slice is the `j`-th partial
derivative. -/
theorem slice_densityDeriv_self (θ : Fin p → ℝ) (j : Fin p) :
    (F.slice θ j).densityDeriv (θ j) = F.partialDeriv j θ := rfl

/-- The mean along the `j`-th slice is the mean at the moved parameter. -/
theorem slice_mean (θ : Fin p → ℝ) (j : Fin p) (T : S → ℝ) (t : ℝ) :
    (F.slice θ j).mean T t = F.mean T (Function.update θ j t) := rfl

/-- The coordinate line through `θ` tends to `θ`. -/
theorem tendsto_update (θ : Fin p → ℝ) (j : Fin p) :
    Tendsto (fun t ↦ Function.update θ j t) (𝓝 (θ j)) (𝓝 θ) := by
  have h := ((continuous_const (y := θ)).update j continuous_id).tendsto (θ j)
  simpa using h

/-- At an interior point of `Θ`, the base point of each slice is interior to its parameter
set. -/
theorem slice_mem_nhds {θ : Fin p → ℝ} (hΘ : F.Θ ∈ 𝓝 θ) (j : Fin p) :
    (F.slice θ j).Θ ∈ 𝓝 (θ j) :=
  tendsto_update θ j hΘ

/-- Under the first order interchange at an interior point, every score component is
`P_θ`-integrable. -/
theorem integrable_scoreVec {θ : Fin p → ℝ} (hΘ : F.Θ ∈ 𝓝 θ) (h1 : F.PartialDerivInterchange θ)
    (j : Fin p) : Integrable (fun x ↦ F.scoreVec θ x j) (F.law θ) := by
  have := (F.slice θ j).integrable_score (slice_mem_nhds hΘ j) (h1 j)
  rwa [slice_law_self, slice_score_self] at this

/-- **The score vector has mean zero**: `E_θ[s_j(θ;X)] = 0` for every `j`, under the first order
interchange at an interior point. -/
theorem integral_scoreVec_eq_zero {θ : Fin p → ℝ} (hΘ : F.Θ ∈ 𝓝 θ)
    (h1 : F.PartialDerivInterchange θ) (j : Fin p) : ∫ x, F.scoreVec θ x j ∂F.law θ = 0 := by
  have := (F.slice θ j).integral_score_eq_zero (slice_mem_nhds hΘ j) (h1 j)
  rwa [slice_law_self, slice_score_self] at this

/-- **The Fisher information matrix is the covariance matrix of the score.** -/
theorem fisherInfoMatrix_eq_covariance {θ : Fin p → ℝ} (hΘ : F.Θ ∈ 𝓝 θ)
    (h1 : F.PartialDerivInterchange θ) (hs : ∀ j, MemLp (fun x ↦ F.scoreVec θ x j) 2 (F.law θ))
    (j k : Fin p) :
    F.fisherInfoMatrix θ j k =
      cov[fun x ↦ F.scoreVec θ x j, fun x ↦ F.scoreVec θ x k; F.law θ] := by
  have := isProbabilityMeasure_law (mem_of_mem_nhds hΘ)
  rw [covariance_eq_sub (hs j) (hs k), integral_scoreVec_eq_zero hΘ h1,
    integral_scoreVec_eq_zero hΘ h1]
  simp [fisherInfoMatrix]

/-- **The gradient of the mean of a statistic is its cross moment with the score vector**:
`∂_j E_θ[T] = E_θ[T s_j(θ;X)]`, with `T s_j` integrable, under the interchange for the mean of
`T` at an interior point. -/
theorem gradMean_eq {T : S → ℝ} {θ : Fin p → ℝ} (hΘ : F.Θ ∈ 𝓝 θ)
    (hT : F.MeanPartialDerivInterchange T θ) (j : Fin p) :
    Integrable (fun x ↦ T x * F.scoreVec θ x j) (F.law θ) ∧
      F.gradMean T θ j = ∫ x, T x * F.scoreVec θ x j ∂F.law θ := by
  have := (F.slice θ j).hasDerivAt_mean (slice_mem_nhds hΘ j) (hT j)
  rw [slice_law_self, slice_score_self] at this
  exact ⟨this.1, this.2.deriv⟩

/-! ### Additivity of information -/

/-- **Additivity of information, vector form.** If `O` is an i.i.d. sample
(`CausalInference.IsIIDSample`) whose observations have law `P_θ`, the sample score
`∑_{i < n} s(θ;O_i)` has mean zero and covariance matrix `n I(θ)`. -/
theorem sum_scoreVec_covariance_of_isIIDSample {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {O : ℕ → Ω → S} (hO : IsIIDSample O μ)
    {θ : Fin p → ℝ} (hlaw : μ.map (O 0) = F.law θ) (hΘ : F.Θ ∈ 𝓝 θ)
    (h1 : F.PartialDerivInterchange θ) (hs : ∀ j, MemLp (fun x ↦ F.scoreVec θ x j) 2 (F.law θ))
    (n : ℕ) :
    (∀ j, μ[fun ω ↦ ∑ i ∈ Finset.range n, F.scoreVec θ (O i ω) j] = 0) ∧
      ∀ j k, cov[fun ω ↦ ∑ i ∈ Finset.range n, F.scoreVec θ (O i ω) j,
        fun ω ↦ ∑ i ∈ Finset.range n, F.scoreVec θ (O i ω) k; μ] =
          n * F.fisherInfoMatrix θ j k := by
  have := isProbabilityMeasure_law (mem_of_mem_nhds hΘ)
  have hlaw' : ∀ i, μ.map (O i) = F.law θ := fun i ↦ (hO.ident i).map_eq.trans hlaw
  have hX : ∀ i, AEMeasurable (O i) μ := hO.aemeasurable
  have hsm : ∀ i j, AEStronglyMeasurable (fun x ↦ F.scoreVec θ x j) (μ.map (O i)) :=
    fun i j ↦ by rw [hlaw' i]; exact (hs j).aestronglyMeasurable
  have hY : ∀ i j, MemLp (fun ω ↦ F.scoreVec θ (O i ω) j) 2 μ := fun i j ↦
    (memLp_map_measure_iff (hsm i j) (hX i)).1 (by rw [hlaw' i]; exact hs j)
  have hfun : ∀ j, (fun ω ↦ ∑ i ∈ Finset.range n, F.scoreVec θ (O i ω) j) =
      ∑ i ∈ Finset.range n, fun ω ↦ F.scoreVec θ (O i ω) j := fun j ↦ by
    ext ω; simp
  refine ⟨fun j ↦ ?_, fun j k ↦ ?_⟩
  · rw [integral_finsetSum _ fun i _ ↦ (hY i j).integrable one_le_two]
    refine Finset.sum_eq_zero fun i _ ↦ ?_
    rw [← integral_map (hX i) (hsm i j), hlaw' i, integral_scoreVec_eq_zero hΘ h1]
  · rw [hfun, hfun, covariance_sum_left' (fun i _ ↦ hY i j)
      (memLp_finsetSum' _ fun i _ ↦ hY i k)]
    simp_rw [covariance_sum_right' (fun i _ ↦ hY i k) (hY _ j)]
    have hdiag : ∀ i, cov[fun ω ↦ F.scoreVec θ (O i ω) j, fun ω ↦ F.scoreVec θ (O i ω) k; μ] =
        F.fisherInfoMatrix θ j k := fun i ↦ by
      rw [fisherInfoMatrix_eq_covariance hΘ h1 hs, ← hlaw' i,
        covariance_map_fun (hsm i j) (hsm i k) (hX i)]
    have hoff : ∀ i l, i ≠ l →
        cov[fun ω ↦ F.scoreVec θ (O i ω) j, fun ω ↦ F.scoreVec θ (O l ω) k; μ] = 0 :=
      fun i l hil ↦ ((hO.indep.indepFun hil).comp₀ (hX i) (hX l) (hsm i j).aemeasurable
        (hsm l k).aemeasurable).covariance_eq_zero (hY i j) (hY l k)
    rw [Finset.sum_congr rfl fun i hi ↦ Finset.sum_eq_single_of_mem i hi fun l _ hli ↦
      hoff i l (Ne.symm hli)]
    simp [hdiag]

/-! ### The information equality -/

/-- The partial derivative of the log-likelihood is `∂_k f / f` where the density is positive and
the coordinate slice is differentiable. -/
theorem partialLogLik_eq {η : Fin p → ℝ} {k : Fin p} {x : S} (hpos : 0 < F.density η x)
    (hd : DifferentiableAt ℝ (fun t ↦ F.density (Function.update η k t) x) (η k)) :
    F.partialLogLik k η x = F.partialDeriv k η x / F.density η x := by
  have hpos' : 0 < F.density (Function.update η k (η k)) x := by simpa using hpos
  rw [partialLogLik, (hd.hasDerivAt.log hpos'.ne').deriv, partialDeriv]
  simp

/-- If `f(x;θ) = 0` and the support does not move near `θ`, every second partial derivative of
the density vanishes at `(x, θ)`. -/
theorem partialDeriv2_eq_zero_of_support {θ : Fin p → ℝ} {x : S} (hΘ : F.Θ ∈ 𝓝 θ)
    (hsupp : ∀ᶠ η in 𝓝 θ, ∀ x, 0 < F.density η x ↔ 0 < F.density θ x)
    (h0 : F.density θ x = 0) (j k : Fin p) : F.partialDeriv2 j k θ x = 0 := by
  have hz : ∀ᶠ η in 𝓝 θ, F.density η x = 0 := by
    filter_upwards [hsupp, hΘ] with η hη hηΘ
    have : ¬ 0 < F.density η x := by rw [hη x, h0]; exact lt_irrefl 0
    exact le_antisymm (not_lt.1 this) (F.density_nonneg η hηΘ x)
  have hz' : ∀ᶠ η in 𝓝 θ, F.partialDeriv k η x = 0 := by
    filter_upwards [eventually_eventually_nhds.2 hz] with η hη
    rw [partialDeriv, Filter.EventuallyEq.deriv_eq (f := fun _ ↦ (0 : ℝ))
      ((tendsto_update η k).eventually hη), deriv_const]
  rw [partialDeriv2, Filter.EventuallyEq.deriv_eq (f := fun _ ↦ (0 : ℝ))
    ((tendsto_update θ j).eventually hz'), deriv_const]

/-- Pointwise form of the information equality, vector form:
`f ∂_j ∂_k ℓ = ∂_j ∂_k f - f s_j s_k`. -/
theorem density_mul_hessianLogLik {θ : Fin p → ℝ} {x : S} (hΘ : F.Θ ∈ 𝓝 θ)
    (hsupp : ∀ᶠ η in 𝓝 θ, ∀ x, 0 < F.density η x ↔ 0 < F.density θ x)
    (hd : ∀ᶠ η in 𝓝 θ, ∀ k,
      DifferentiableAt ℝ (fun t ↦ F.density (Function.update η k t) x) (η k))
    {j k : Fin p}
    (hd2 : DifferentiableAt ℝ (fun t ↦ F.partialDeriv k (Function.update θ j t) x) (θ j)) :
    F.density θ x * F.hessianLogLik j k θ x =
      F.partialDeriv2 j k θ x - F.density θ x * (F.scoreVec θ x j * F.scoreVec θ x k) := by
  rcases (F.density_nonneg θ (mem_of_mem_nhds hΘ) x).eq_or_lt with h0 | hpos
  · rw [← h0, partialDeriv2_eq_zero_of_support hΘ hsupp h0.symm]
    ring
  · have hdj : DifferentiableAt ℝ (fun t ↦ F.density (Function.update θ j t) x) (θ j) :=
      hd.self_of_nhds j
    have hposj : 0 < F.density (Function.update θ j (θ j)) x := by simpa using hpos
    have hposn : ∀ᶠ t in 𝓝 (θ j), 0 < F.density (Function.update θ j t) x :=
      hdj.continuousAt.eventually (lt_mem_nhds hposj)
    have heq : (fun t ↦ F.partialLogLik k (Function.update θ j t) x) =ᶠ[𝓝 (θ j)]
        fun t ↦ F.partialDeriv k (Function.update θ j t) x /
          F.density (Function.update θ j t) x := by
      filter_upwards [hposn, (tendsto_update θ j).eventually hd] with t ht hdt
      exact partialLogLik_eq ht (hdt k)
    have hder : HasDerivAt (fun t ↦ F.partialDeriv k (Function.update θ j t) x /
        F.density (Function.update θ j t) x) _ (θ j) :=
      hd2.hasDerivAt.div hdj.hasDerivAt hposj.ne'
    have e1 : deriv (fun t ↦ F.density (Function.update θ j t) x) (θ j) =
      F.partialDeriv j θ x := rfl
    have e2 : deriv (fun t ↦ F.partialDeriv k (Function.update θ j t) x) (θ j) =
      F.partialDeriv2 j k θ x := rfl
    rw [hessianLogLik, heq.deriv_eq, hder.deriv, e1, e2]
    simp only [Function.update_eq_self, scoreVec]
    field_simp

/-- **The information equality, vector form.** At an interior point with common support near
`θ`, almost everywhere differentiability of the coordinate slices of `f` near `θ` and of those of
`∂_k f` at `θ`, the first order interchange near `θ`, the second order interchange at `θ`, and a
square integrable score: every `∂_j ∂_k ℓ(θ;·)` is `P_θ`-integrable and
`I(θ)_{jk} = -E_θ[∂_j ∂_k ℓ(θ;X)]`. -/
theorem information_equality_vec {θ : Fin p → ℝ} (hΘ : F.Θ ∈ 𝓝 θ)
    (hsupp : ∀ᶠ η in 𝓝 θ, ∀ x, 0 < F.density η x ↔ 0 < F.density θ x)
    (hdiff : ∀ᵐ x ∂F.ν,
      (∀ᶠ η in 𝓝 θ, ∀ k,
        DifferentiableAt ℝ (fun t ↦ F.density (Function.update η k t) x) (η k)) ∧
      ∀ j k, DifferentiableAt ℝ (fun t ↦ F.partialDeriv k (Function.update θ j t) x) (θ j))
    (h1 : ∀ᶠ η in 𝓝 θ, F.PartialDerivInterchange η) (h2 : F.PartialDerivInterchangeTwo θ)
    (hs : ∀ j, MemLp (fun x ↦ F.scoreVec θ x j) 2 (F.law θ)) (j k : Fin p) :
    Integrable (F.hessianLogLik j k θ) (F.law θ) ∧
      F.fisherInfoMatrix θ j k = -∫ x, F.hessianLogLik j k θ x ∂F.law θ := by
  have hθ : θ ∈ F.Θ := mem_of_mem_nhds hΘ
  have hzero1 : ∀ᶠ η in 𝓝 θ, ∫ x, F.partialDeriv k η x ∂F.ν = 0 := by
    filter_upwards [h1, eventually_mem_nhds_iff.2 hΘ] with η hη hηΘ
    exact (F.slice η k).integral_densityDeriv_eq_zero (slice_mem_nhds hηΘ k) (hη k)
  have hzero2 : ∫ x, F.partialDeriv2 j k θ x ∂F.ν = 0 :=
    (h2 j k).2.unique ((hasDerivAt_const (θ j) (0 : ℝ)).congr_of_eventuallyEq
      ((tendsto_update θ j).eventually hzero1))
  have hsq : Integrable (fun x ↦ F.density θ x * (F.scoreVec θ x j * F.scoreVec θ x k)) F.ν :=
    (integrable_law_iff hθ).1 ((hs j).integrable_mul (hs k))
  have hpt : (fun x ↦ F.density θ x * F.hessianLogLik j k θ x) =ᵐ[F.ν]
      fun x ↦ F.partialDeriv2 j k θ x - F.density θ x * (F.scoreVec θ x j * F.scoreVec θ x k) :=
    hdiff.mono fun x hx ↦ density_mul_hessianLogLik hΘ hsupp hx.1 (hx.2 j k)
  refine ⟨(integrable_law_iff hθ).2 (((h2 j k).1.sub hsq).congr hpt.symm), ?_⟩
  rw [integral_law hθ, integral_congr_ae hpt, integral_sub (h2 j k).1 hsq, hzero2,
    fisherInfoMatrix, of_apply, integral_law hθ]
  ring

/-! ### Interchange from envelopes and regular points -/

/-- Moving the `j`-th coordinate twice: the slice of `update η j t` is the slice of `η`. -/
theorem partialDeriv_update (η : Fin p → ℝ) (j : Fin p) (t : ℝ) (x : S) :
    F.partialDeriv j (Function.update η j t) x =
      deriv (fun v ↦ F.density (Function.update η j v) x) t := by
  simp [partialDeriv]

/-- If `η ↦ f(x;η)` is `C²` on a ball, its coordinate slices are differentiable at every point of
the ball. -/
theorem hasDerivAt_slice_of_contDiffOn {θ : Fin p → ℝ} {ε : ℝ} {x : S}
    (hC : ContDiffOn ℝ 2 (fun η ↦ F.density η x) (ball θ ε)) {η : Fin p → ℝ} (k : Fin p) {t : ℝ}
    (ht : Function.update η k t ∈ ball θ ε) :
    HasDerivAt (fun v ↦ F.density (Function.update η k v) x)
      (fderiv ℝ (fun η ↦ F.density η x) (Function.update η k t) (Pi.single k 1)) t := by
  have h := (hC.differentiableOn (by norm_num)).differentiableAt (isOpen_ball.mem_nhds ht)
  exact h.hasFDerivAt.comp_hasDerivAt t (hasDerivAt_update η k t)

/-- If `η ↦ f(x;η)` is `C²` on a ball, the coordinate slices of each partial derivative are
differentiable at every point of the ball. -/
theorem differentiableAt_partialDeriv_of_contDiffOn {θ : Fin p → ℝ} {ε : ℝ} {x : S}
    (hC : ContDiffOn ℝ 2 (fun η ↦ F.density η x) (ball θ ε)) {η : Fin p → ℝ}
    (hη : η ∈ ball θ ε) (j k : Fin p) :
    DifferentiableAt ℝ (fun t ↦ F.partialDeriv k (Function.update η j t) x) (η j) := by
  set g : (Fin p → ℝ) → ℝ := fun η ↦ F.density η x with hg
  have hpart : (fun t ↦ F.partialDeriv k (Function.update η j t) x) =ᶠ[𝓝 (η j)]
      fun t ↦ fderiv ℝ g (Function.update η j t) (Pi.single k 1) := by
    filter_upwards [(tendsto_update η j).eventually (isOpen_ball.mem_nhds hη)] with t ht
    have h := hasDerivAt_slice_of_contDiffOn hC (η := Function.update η j t) k
      (t := Function.update η j t k) (by simpa using ht)
    rw [partialDeriv, h.deriv, Function.update_eq_self]
  have hfd : DifferentiableAt ℝ (fderiv ℝ g) η :=
    ((hC.fderiv_of_isOpen isOpen_ball (m := 1) (by norm_num)).differentiableOn
      (by norm_num)).differentiableAt (isOpen_ball.mem_nhds hη)
  have hfd' : DifferentiableAt ℝ (fun y ↦ fderiv ℝ g y (Pi.single k 1))
      (Function.update η j (η j)) := by
    simpa using hfd.clm_apply (differentiableAt_const (Pi.single k (1 : ℝ)))
  exact (hfd'.comp (η j) (hasDerivAt_update η j (η j)).differentiableAt).congr_of_eventuallyEq
    hpart

/-- If `η ↦ f(x;η)` is `C²` on a ball around `θ`, the coordinate slices of the density are
differentiable near `θ` and those of each partial derivative are differentiable at `θ`. -/
theorem differentiable_of_contDiffOn {θ : Fin p → ℝ} {ε : ℝ} (hε : 0 < ε) {x : S}
    (hC : ContDiffOn ℝ 2 (fun η ↦ F.density η x) (ball θ ε)) :
    (∀ᶠ η in 𝓝 θ, ∀ k,
      DifferentiableAt ℝ (fun t ↦ F.density (Function.update η k t) x) (η k)) ∧
      ∀ j k, DifferentiableAt ℝ (fun t ↦ F.partialDeriv k (Function.update θ j t) x) (θ j) :=
  ⟨eventually_of_mem (ball_mem_nhds θ hε) fun η hη k ↦
    (hasDerivAt_slice_of_contDiffOn hC k (by simpa using hη)).differentiableAt,
    fun j k ↦ differentiableAt_partialDeriv_of_contDiffOn hC (mem_ball_self hε) j k⟩

/-- Points of a coordinate line through `η ∈ ball θ (ε / 2)` at distance `< ε / 2` from `η` lie
in `ball θ ε`. -/
theorem update_mem_ball {θ η : Fin p → ℝ} {ε : ℝ} (hε : 0 < ε) (hη : η ∈ ball θ (ε / 2))
    (k : Fin p) {t : ℝ} (ht : t ∈ ball (η k) (ε / 2)) : Function.update η k t ∈ ball θ ε := by
  rw [mem_ball] at hη ht ⊢
  refine (dist_pi_lt_iff hε).2 fun i ↦ ?_
  have hi : dist (η i) (θ i) < ε / 2 := lt_of_le_of_lt (dist_le_pi_dist η θ i) hη
  by_cases hik : i = k
  · subst hik
    rw [Function.update_self]
    have := dist_triangle t (η i) (θ i)
    linarith
  · rw [Function.update_of_ne hik]; linarith

/-- **Interchange from envelopes, vector form.** If the density is almost everywhere `C²` in the
parameter on a ball around `θ` contained in `Θ`, and its first and second partial derivatives are
bounded there by integrable envelopes `b₁`, `b₂`, then the first order interchange holds near `θ`
and the second order interchange at `θ`. Proof: dominated convergence along coordinate lines. -/
theorem interchange_of_dominated {θ : Fin p → ℝ} {ε : ℝ} (hε : 0 < ε) (hball : ball θ ε ⊆ F.Θ)
    (hC : ∀ᵐ x ∂F.ν, ContDiffOn ℝ 2 (fun η ↦ F.density η x) (ball θ ε)) {b₁ b₂ : S → ℝ}
    (hb₁ : Integrable b₁ F.ν) (hb₂ : Integrable b₂ F.ν)
    (hbound : ∀ᵐ x ∂F.ν, ∀ η ∈ ball θ ε, ∀ j k,
      |F.partialDeriv k η x| ≤ b₁ x ∧ |F.partialDeriv2 j k η x| ≤ b₂ x) :
    (∀ᶠ η in 𝓝 θ, F.PartialDerivInterchange η) ∧ F.PartialDerivInterchangeTwo θ := by
  have hε2 : 0 < ε / 2 := half_pos hε
  have h1 : ∀ η ∈ ball θ (ε / 2), F.PartialDerivInterchange η := by
    intro η hη k
    exact (F.slice η k).derivInterchange_of_dominated (θ := η k) (ε := ε / 2)
      (fun t ht ↦ hball (update_mem_ball hε hη k ht)) hb₁
      (hC.mono fun x hx t ht ↦ (hasDerivAt_slice_of_contDiffOn hx k
        (update_mem_ball hε hη k ht)).differentiableAt)
      (hbound.mono fun x hx t ht ↦ by
        have := (hx _ (update_mem_ball hε hη k ht) k k).1
        rwa [partialDeriv_update] at this) (η k) (mem_ball_self hε2)
  refine ⟨eventually_of_mem (ball_mem_nhds θ hε2) h1, fun j k ↦ ?_⟩
  have hmem : ∀ t ∈ ball (θ j) (ε / 2), Function.update θ j t ∈ ball θ (ε / 2) := by
    intro t ht
    rw [mem_ball] at ht ⊢
    refine (dist_pi_lt_iff hε2).2 fun i ↦ ?_
    by_cases hij : i = j
    · subst hij; rw [Function.update_self]; exact ht
    · rw [Function.update_of_ne hij, dist_self]; exact hε2
  have hG : ∀ t ∈ ball (θ j) (ε / 2),
      AEStronglyMeasurable (F.partialDeriv k (Function.update θ j t)) F.ν :=
    fun t ht ↦ ((h1 _ (hmem t ht) k).1).aestronglyMeasurable
  have hmeas : AEStronglyMeasurable (F.partialDeriv2 j k θ) F.ν :=
    aestronglyMeasurable_deriv (G := fun t x ↦ F.partialDeriv k (Function.update θ j t) x) hε2 hG
      (hC.mono fun x hx ↦ differentiableAt_partialDeriv_of_contDiffOn hx (mem_ball_self hε) j k)
  have hθint : Integrable (F.partialDeriv k (Function.update θ j (θ j))) F.ν := by
    rw [Function.update_eq_self]; exact (h1 θ (mem_ball_self hε2) k).1
  have hsub : ∀ t ∈ ball (θ j) (ε / 2), Function.update θ j t ∈ ball θ ε :=
    fun t ht ↦ ball_subset_ball (half_le_self hε.le) (hmem t ht)
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (ball_mem_nhds (θ j) hε2)
    (F := fun t x ↦ F.partialDeriv k (Function.update θ j t) x)
    (F' := fun t x ↦ F.partialDeriv2 j k (Function.update θ j t) x) (bound := b₂)
    (eventually_of_mem (ball_mem_nhds (θ j) hε2) hG) hθint
    (by rw [Function.update_eq_self]; exact hmeas)
    (hbound.mono fun x hx t ht ↦ by rw [Real.norm_eq_abs]; exact (hx _ (hsub t ht) j k).2) hb₂
    (hC.mono fun x hx t ht ↦ by
      have hd := differentiableAt_partialDeriv_of_contDiffOn hx (hsub t ht) j k
      have e : (fun s ↦ F.partialDeriv k (Function.update (Function.update θ j t) j s) x) =
          fun s ↦ F.partialDeriv k (Function.update θ j s) x := by
        ext s; rw [Function.update_idem]
      rw [e, Function.update_self] at hd
      have e2 : F.partialDeriv2 j k (Function.update θ j t) x =
          deriv (fun s ↦ F.partialDeriv k (Function.update θ j s) x) t := by
        rw [partialDeriv2, Function.update_self]
        simp only [Function.update_idem]
      rw [e2]
      exact hd.hasDerivAt)
  rw [Function.update_eq_self] at key
  exact key

variable (F) in
/-- A regular point `θ` of a vector family, with conditions that a concrete family can check:
common support near `θ`; on a ball around `θ` contained in `Θ`, `η ↦ f(x;η)` is twice
continuously differentiable for `ν`-almost every `x`, and the first and second partial
derivatives have `ν`-integrable envelopes there; the score is square integrable. -/
structure IsRegularAtVec (θ : Fin p → ℝ) : Prop where
  /-- Common support near `θ`. -/
  support : ∀ᶠ η in 𝓝 θ, ∀ x, 0 < F.density η x ↔ 0 < F.density θ x
  /-- Smoothness and envelopes on a ball inside `Θ`. -/
  smooth_dominated : ∃ ε > 0, ball θ ε ⊆ F.Θ ∧
    (∀ᵐ x ∂F.ν, ContDiffOn ℝ 2 (fun η ↦ F.density η x) (ball θ ε)) ∧
    ∃ b₁ b₂ : S → ℝ, Integrable b₁ F.ν ∧ Integrable b₂ F.ν ∧
      ∀ᵐ x ∂F.ν, ∀ η ∈ ball θ ε, ∀ j k,
        |F.partialDeriv k η x| ≤ b₁ x ∧ |F.partialDeriv2 j k η x| ≤ b₂ x
  /-- The score vector is square integrable. -/
  memLp_scoreVec : ∀ j, MemLp (fun x ↦ F.scoreVec θ x j) 2 (F.law θ)

namespace IsRegularAtVec

variable {θ : Fin p → ℝ}

/-- A regular point is interior to `Θ`. -/
theorem mem_nhds (h : F.IsRegularAtVec θ) : F.Θ ∈ 𝓝 θ := by
  obtain ⟨ε, hε, hball, -⟩ := h.smooth_dominated
  exact Filter.mem_of_superset (ball_mem_nhds θ hε) hball

/-- At a regular point both interchanges hold. -/
theorem interchange (h : F.IsRegularAtVec θ) :
    (∀ᶠ η in 𝓝 θ, F.PartialDerivInterchange η) ∧ F.PartialDerivInterchangeTwo θ := by
  obtain ⟨ε, hε, hball, hC, b₁, b₂, hb₁, hb₂, hbd⟩ := h.smooth_dominated
  exact interchange_of_dominated hε hball hC hb₁ hb₂ hbd

/-- **The information equality at a regular point**: `I(θ)_{jk} = Cov_θ(s_j, s_k)` and
`I(θ)_{jk} = -E_θ[∂_j ∂_k ℓ(θ;X)]`, with `∂_j ∂_k ℓ(θ;·)` integrable. -/
theorem information_equality (h : F.IsRegularAtVec θ) (j k : Fin p) :
    F.fisherInfoMatrix θ j k =
        cov[fun x ↦ F.scoreVec θ x j, fun x ↦ F.scoreVec θ x k; F.law θ] ∧
      Integrable (F.hessianLogLik j k θ) (F.law θ) ∧
      F.fisherInfoMatrix θ j k = -∫ x, F.hessianLogLik j k θ x ∂F.law θ := by
  refine ⟨fisherInfoMatrix_eq_covariance h.mem_nhds h.interchange.1.self_of_nhds
    h.memLp_scoreVec j k, ?_⟩
  obtain ⟨ε, hε, -, hC, -⟩ := h.smooth_dominated
  exact information_equality_vec h.mem_nhds h.support
    (hC.mono fun x hx ↦ differentiable_of_contDiffOn hε hx) h.interchange.1
    h.interchange.2 h.memLp_scoreVec j k

end IsRegularAtVec

end ParametricFamily

end CausalInference
