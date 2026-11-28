/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.Estimation.BootstrapMeanLimit
public import CausalInference.Estimation.TriangularArrayLimitVector
public import CausalInference.Estimation.VectorCLT
public import CausalInference.Estimation.BootstrapCoverage

/-!
# The conditional central limit theorem of the vector bootstrap mean

The vector form of `CausalInference.Estimation.BootstrapMeanLimit`. Along a fixed data path, a
centered family `g n : 𝒪 → ℝ^ι` whose empirical second moments in every direction converge to
`tᵀ S t` and whose norms satisfy the empirical Lindeberg condition gives a resampled normalized
sum converging in law to `N(0, S)` (`Bootstrap.tendstoInDistribution_resample_of_path_euclidean`,
from the vector Lindeberg theorem `TriangularArray.tendstoInDistribution_sum_euclidean`). Almost
surely the directional empirical second moments converge for every `t` at once
(`Bootstrap.ae_tendsto_inner_sq`).

For an i.i.d. sample and `f : 𝒪 → ℝ^ι` with `E‖f(O_0)‖² < ∞` the hypotheses hold almost surely:
the empirical cross moments `n⁻¹ ∑_{k < n} f_i(O_k) f_j(O_k)` converge for the finitely many pairs
`(i, j)` by the strong law, which gives the directional second moments for every `t` at once,
and the Lindeberg condition follows from the real one for `‖f‖ + C`. Hence, for almost every data
path, `√n (X̄*_n - X̄_n)` given the data converges in law to `N(0, Σ)`, with `Σ` the covariance
matrix of `f(O_0)` (`Bootstrap.ae_tendstoInDistribution_resampleMean_euclidean`), and the
bootstrap laws converge weakly to `N(0, Σ)` in probability
(`Bootstrap.isBernsteinVonMisesWeak_resampleMeanVec`). For `Ψ` strictly differentiable at the
mean with a nondegenerate linearization, the percentile interval of the bootstrap law of
`Ψ(X̄*_n)` covers `Ψ(E f(O_0))` with probability tending to `1 - α`
(`Bootstrap.tendsto_bootstrap_delta_coverage`, the bootstrap delta method).

## References

* P. J. Bickel and D. A. Freedman (1981), *Some asymptotic theory for the bootstrap*, Annals of
  Statistics 9.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Finset Topology Matrix
open scoped ENNReal NNReal RealInnerProductSpace BoundedContinuousFunction

namespace CausalInference

namespace Bootstrap

open BiasAnalysis.MeasurementError (covMatrix)
open PosteriorLimit

variable {Ω 𝒪 : Type*} {mΩ : MeasurableSpace Ω} [MeasurableSpace 𝒪]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ### Tools -/

/-- Integrating a strongly measurable vector function against the empirical measure gives the
vector sample mean `n⁻¹ • ∑_{k < n} f (O k ω)`. -/
theorem integral_empiricalMeasure_eq_smul_sum {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] {f : 𝒪 → E} (hf : StronglyMeasurable f) (O : ℕ → Ω → 𝒪)
    (n : ℕ) (ω : Ω) :
    ∫ x, f x ∂(empiricalMeasure O n ω) = (n : ℝ)⁻¹ • ∑ k ∈ range n, f (O k ω) := by
  rw [empiricalMeasure, integral_smul_measure, integral_finsetSum_measure]
  · simp [integral_dirac' _ _ hf]
  · intro i _
    exact integrable_dirac' hf (by simp)

/-- Integrals of a vector function of one resampled observation are vector sample means. -/
theorem integral_comp_eval_resampleLaw_smul {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] {g : 𝒪 → E} (hg : StronglyMeasurable g) (O : ℕ → Ω → 𝒪)
    (n : ℕ) (ω : Ω) (i : Fin n) :
    ∫ y, g (y i) ∂resampleLaw O n ω = (n : ℝ)⁻¹ • ∑ k ∈ range n, g (O k ω) := by
  rw [← integral_map (measurable_pi_apply i).aemeasurable hg.aestronglyMeasurable,
    (hasLaw_eval_resampleLaw O n ω i).map_eq, integral_empiricalMeasure_eq_smul_sum hg]

/-- A Lindeberg term of a vector is the real Lindeberg term of its norm. -/
theorem indicator_norm_sq_eq {E : Type*} [NormedAddCommGroup E] (c : ℝ) (v : E) :
    {y : E | c < ‖y‖}.indicator (fun y ↦ ‖y‖ ^ 2) v =
      {x : ℝ | c < |x|}.indicator (fun x ↦ x ^ 2) ‖v‖ := by
  by_cases h : c < ‖v‖
  · rw [Set.indicator_of_mem (show v ∈ {y : E | c < ‖y‖} from h),
      Set.indicator_of_mem (show ‖v‖ ∈ {x : ℝ | c < |x|} by simpa [abs_norm] using h)]
  · rw [Set.indicator_of_notMem (show v ∉ {y : E | c < ‖y‖} from h),
      Set.indicator_of_notMem (show ‖v‖ ∉ {x : ℝ | c < |x|} by simpa [abs_norm] using h)]

omit [DecidableEq ι] in
/-- The square of a projection as a quadratic form in the coordinates:
`⟪y, t⟫² = ∑_i ∑_j t_i t_j y_i y_j`. -/
theorem inner_sq_eq_sum (y t : EuclideanSpace ℝ ι) :
    ⟪y, t⟫ ^ 2 = ∑ i, ∑ j, t i * t j * (y i * y j) := by
  rw [sq, PiLp.inner_apply, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ ?_
  simp only [RCLike.inner_apply, conj_trivial]
  ring

/-! ### The central limit theorem along a data path -/

/-- **The vector bootstrap central limit theorem along a fixed data path.** Fix the data path
`ω` and measurable `g n : 𝒪 → ℝ^ι`, eventually centered along the path, with directional empirical
second moments `n⁻¹ ∑_{k < n} ⟪g n (O k ω), t⟫² → tᵀ S t` for every `t` (`S` positive
semidefinite) and the empirical Lindeberg condition
`n⁻¹ ∑_{k < n} ‖g n (O k ω)‖² 1{ε √n < ‖g n (O k ω)‖} → 0` for every `ε > 0`. Then under
resampling from the empirical law of the path, `n^{-1/2} ∑_i g n (y i)` converges in
distribution to every `Y` with law `N(0, S)`. -/
theorem tendstoInDistribution_resample_of_path_euclidean {O : ℕ → Ω → 𝒪} {ω : Ω}
    {g : ℕ → 𝒪 → EuclideanSpace ℝ ι} (hg : ∀ n, Measurable (g n))
    (h0 : ∀ᶠ n in atTop, ∑ k ∈ range n, g n (O k ω) = 0) {S : Matrix ι ι ℝ} (hS : S.PosSemidef)
    (hcov : ∀ t, Tendsto (fun n : ℕ ↦ (n : ℝ)⁻¹ * ∑ k ∈ range n, ⟪g n (O k ω), t⟫ ^ 2) atTop
      (𝓝 (WithLp.ofLp t ⬝ᵥ S *ᵥ WithLp.ofLp t)))
    (hL : ∀ ε, 0 < ε → Tendsto (fun n : ℕ ↦ (n : ℝ)⁻¹ * ∑ k ∈ range n,
      {x : ℝ | ε * √(n : ℝ) < |x|}.indicator (fun x ↦ x ^ 2) ‖g n (O k ω)‖) atTop (𝓝 0))
    {Ω' : Type*} {mΩ' : MeasurableSpace Ω'} {P' : Measure Ω'} [IsProbabilityMeasure P']
    {Y : Ω' → EuclideanSpace ℝ ι} (hY : HasLaw Y (multivariateGaussian 0 S) P') :
    TendstoInDistribution (fun (n : ℕ) (y : Fin n → 𝒪) ↦ (√(n : ℝ))⁻¹ • ∑ i, g n (y i)) atTop
      Y (fun n ↦ resampleLaw O n ω) P' := by
  classical
  set q : ℕ → Prop := fun n ↦ 1 ≤ n ∧ ∑ k ∈ range n, g n (O k ω) = 0 with hq
  have hqe : ∀ᶠ n in atTop, q n := (eventually_ge_atTop 1).and h0
  set g' : ℕ → 𝒪 → EuclideanSpace ℝ ι := fun n ↦ if q n then g n else 0 with hg'
  have hg'm : ∀ n, Measurable (g' n) := fun n ↦ by
    simp only [hg']
    split_ifs
    exacts [hg n, measurable_const]
  have hgq : ∀ n, q n → g' n = g n := fun n hn ↦ by simp [hg', hn]
  set X : (n : ℕ) → Fin n → (Fin n → 𝒪) → EuclideanSpace ℝ ι :=
    fun n i y ↦ (√(n : ℝ))⁻¹ • g' n (y i) with hX
  have hind : ∀ n, iIndepFun (X n) (resampleLaw O n ω) := fun n ↦
    (iIndepFun_resampleLaw O n ω).comp (fun _ x ↦ (√(n : ℝ))⁻¹ • g' n x)
      fun _ ↦ by have := hg'm n; fun_prop
  have h2 : ∀ n i, MemLp (X n i) 2 (resampleLaw O n ω) := fun n i ↦
    (memLp_comp_eval_resampleLaw (hg'm n).stronglyMeasurable O n ω i).const_smul
      ((√(n : ℝ))⁻¹)
  have hsum0 : ∀ n, ∑ k ∈ range n, g' n (O k ω) = 0 := by
    intro n
    by_cases hn : q n
    · rw [hgq n hn, hn.2]
    · simp [hg', hn]
  have h0' : ∀ n i, ∫ y, X n i y ∂resampleLaw O n ω = 0 := fun n i ↦ by
    simp only [hX]
    rw [integral_smul, integral_comp_eval_resampleLaw_smul (hg'm n).stronglyMeasurable, hsum0,
      smul_zero, smul_zero]
  have hcard : ∀ n (c : ℝ), ∑ _i : Fin n, c = n * c := fun n c ↦ by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hcov' : ∀ t, Tendsto (fun n ↦ ∑ i, ∫ y, ⟪X n i y, t⟫ ^ 2 ∂resampleLaw O n ω) atTop
      (𝓝 (WithLp.ofLp t ⬝ᵥ S *ᵥ WithLp.ofLp t)) := by
    intro t
    refine (hcov t).congr' (hqe.mono fun n hn ↦ ?_)
    have hn0 : (n : ℝ) ≠ 0 := by have := hn.1; positivity
    have hpt : ∀ i, ∫ y, ⟪X n i y, t⟫ ^ 2 ∂resampleLaw O n ω =
        (n : ℝ)⁻¹ * sampleMean (fun z ↦ ⟪g' n z, t⟫ ^ 2) O n ω := by
      intro i
      have : (fun y : Fin n → 𝒪 ↦ ⟪X n i y, t⟫ ^ 2) =
          fun y ↦ (n : ℝ)⁻¹ * ⟪g' n (y i), t⟫ ^ 2 := by
        funext y
        simp only [hX]
        rw [inner_smul_left, conj_trivial, mul_pow, inv_pow,
          Real.sq_sqrt (Nat.cast_nonneg _)]
      rw [this, integral_const_mul, integral_comp_eval_resampleLaw
        (g := fun z ↦ ⟪g' n z, t⟫ ^ 2) (by fun_prop)]
    simp only [hpt, hcard, sampleMean, hgq n hn]
    field_simp
  have hL' : ∀ ε, 0 < ε → Tendsto (fun n ↦ ∑ i, ∫ y,
      {z : EuclideanSpace ℝ ι | ε < ‖z‖}.indicator (fun z ↦ ‖z‖ ^ 2) (X n i y)
        ∂resampleLaw O n ω) atTop (𝓝 0) := by
    intro ε hε
    refine (hL ε hε).congr' (hqe.mono fun n hn ↦ ?_)
    have hn0 : (n : ℝ) ≠ 0 := by have := hn.1; positivity
    have hr : 0 ≤ (√(n : ℝ))⁻¹ := inv_nonneg.2 (Real.sqrt_nonneg _)
    have hAm : MeasurableSet {x : ℝ | ε * √(n : ℝ) < |x|} :=
      measurableSet_lt measurable_const (by fun_prop)
    have hpt : ∀ i, ∫ y, {z : EuclideanSpace ℝ ι | ε < ‖z‖}.indicator (fun z ↦ ‖z‖ ^ 2)
        (X n i y) ∂resampleLaw O n ω = (n : ℝ)⁻¹ * sampleMean
          (fun z ↦ {x : ℝ | ε * √(n : ℝ) < |x|}.indicator (fun x ↦ x ^ 2) ‖g' n z‖) O n ω := by
      intro i
      have : (fun y : Fin n → 𝒪 ↦ {z : EuclideanSpace ℝ ι | ε < ‖z‖}.indicator
          (fun z ↦ ‖z‖ ^ 2) (X n i y)) = fun y ↦ (n : ℝ)⁻¹ *
            {x : ℝ | ε * √(n : ℝ) < |x|}.indicator (fun x ↦ x ^ 2) ‖g' n (y i)‖ := by
        funext y
        simp only [hX]
        rw [indicator_norm_sq_eq, norm_smul, Real.norm_of_nonneg hr,
          indicator_inv_sqrt_mul hn.1]
      rw [this, integral_const_mul, integral_comp_eval_resampleLaw
        (g := fun z ↦ {x : ℝ | ε * √(n : ℝ) < |x|}.indicator (fun x ↦ x ^ 2) ‖g' n z‖)
        (((measurable_id.pow_const 2).indicator hAm).comp (hg'm n).norm)]
    simp only [hpt, hcard, sampleMean, hgq n hn]
    field_simp
  have hclt := TriangularArray.tendstoInDistribution_sum_euclidean hind h2 h0' hS hcov' hL' hY
  refine tendstoInDistribution_congr_eventually hclt (hqe.mono fun n hn ↦ ?_) fun n ↦ ?_
  · funext y
    simp only [hX, hgq n hn, Finset.smul_sum]
  · have hs : Measurable fun y : Fin n → 𝒪 ↦ ∑ i, g n (y i) :=
      Finset.measurable_fun_sum _ fun i _ ↦ (hg n).comp (measurable_pi_apply i)
    exact Measurable.aemeasurable (by fun_prop)

/-! ### Empirical second moments along almost every path -/

omit [DecidableEq ι] in
/-- **The empirical second moments converge in every direction almost surely.** For an i.i.d.
sample and a measurable `g : 𝒪 → ℝ^ι` with `E‖g(O_0)‖² < ∞`, almost surely, for every `t`,
`n⁻¹ ∑_{k < n} ⟪g(O_k), t⟫² → E⟪g(O_0), t⟫²`. The strong law for the finitely many products
`g_i g_j` and the expansion `⟪y, t⟫² = ∑_i ∑_j t_i t_j y_i y_j` give every `t` at once. -/
theorem ae_tendsto_inner_sq {P : Measure Ω} [IsProbabilityMeasure P] {O : ℕ → Ω → 𝒪}
    (hO : IsIIDSample O P) {g : 𝒪 → EuclideanSpace ℝ ι} (hg : Measurable g)
    (hg2 : MemLp (fun ω ↦ g (O 0 ω)) 2 P) :
    ∀ᵐ ω ∂P, ∀ t : EuclideanSpace ℝ ι, Tendsto (fun n : ℕ ↦
      (n : ℝ)⁻¹ * ∑ k ∈ range n, ⟪g (O k ω), t⟫ ^ 2) atTop
      (𝓝 (P[fun ω ↦ ⟪g (O 0 ω), t⟫ ^ 2])) := by
  have hc : ∀ i, MemLp (fun ω ↦ g (O 0 ω) i) 2 P := fun i ↦
    (EuclideanSpace.proj (𝕜 := ℝ) i).comp_memLp' hg2
  have hgi : ∀ i, Measurable fun z ↦ g z i := fun i ↦
    (EuclideanSpace.proj (𝕜 := ℝ) i).continuous.measurable.comp hg
  have hprod : ∀ᵐ ω ∂P, ∀ p : ι × ι, Tendsto (fun n : ℕ ↦ (n : ℝ)⁻¹ • ∑ k ∈ range n,
      g (O k ω) p.1 * g (O k ω) p.2) atTop (𝓝 (P[fun ω ↦ g (O 0 ω) p.1 * g (O 0 ω) p.2])) :=
    ae_all_iff.2 fun p ↦ hO.tendsto_ae_smul_sum (f := fun z ↦ g z p.1 * g z p.2)
      ((hgi p.1).mul (hgi p.2)) ((hc p.1).integrable_mul (hc p.2))
  filter_upwards [hprod] with ω hω2 t
  have hEQ : ∑ i, ∑ j, t i * t j * P[fun ω ↦ g (O 0 ω) i * g (O 0 ω) j] =
      P[fun ω ↦ ⟪g (O 0 ω), t⟫ ^ 2] := by
    have hij : ∀ i j, Integrable (fun ω ↦ t i * t j * (g (O 0 ω) i * g (O 0 ω) j)) P :=
      fun i j ↦ ((hc i).integrable_mul (hc j)).const_mul _
    simp only [inner_sq_eq_sum]
    rw [integral_finsetSum _ fun i _ ↦ integrable_finsetSum _ fun j _ ↦ hij i j]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [integral_finsetSum _ fun j _ ↦ hij i j]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [integral_const_mul]
  rw [← hEQ]
  have hlim : Tendsto (fun n : ℕ ↦ ∑ i, ∑ j, t i * t j *
      ((n : ℝ)⁻¹ • ∑ k ∈ range n, g (O k ω) i * g (O k ω) j)) atTop
      (𝓝 (∑ i, ∑ j, t i * t j * P[fun ω ↦ g (O 0 ω) i * g (O 0 ω) j])) :=
    tendsto_finsetSum _ fun i _ ↦ tendsto_finsetSum _ fun j _ ↦
      (hω2 (i, j)).const_mul (t i * t j)
  refine hlim.congr fun n ↦ ?_
  simp only [smul_eq_mul, inner_sq_eq_sum, Finset.mul_sum]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ ↦ Finset.sum_congr rfl fun k _ ↦ ?_
  ring

/-! ### The bootstrap of the vector mean -/

/-- **The conditional central limit theorem of the vector bootstrap mean.** Let `O` be an i.i.d.
sample and `f : 𝒪 → ℝ^ι` measurable with `E‖f(O_0)‖² < ∞`. For almost every data path `ω`, under
resampling from the empirical law of the first `n` observations,
`√n (n⁻¹ ∑_i f(y_i) - n⁻¹ ∑_{k < n} f(O_k ω))` converges in distribution to `N(0, Σ)`, with `Σ`
the covariance matrix of the coordinates of `f(O_0)`. -/
theorem ae_tendstoInDistribution_resampleMean_euclidean {P : Measure Ω} [IsProbabilityMeasure P]
    {O : ℕ → Ω → 𝒪} (hO : IsIIDSample O P) {f : 𝒪 → EuclideanSpace ℝ ι} (hf : Measurable f)
    (hf2 : MemLp (fun ω ↦ f (O 0 ω)) 2 P) :
    ∀ᵐ ω ∂P, TendstoInDistribution
      (fun (n : ℕ) (y : Fin n → 𝒪) ↦ √(n : ℝ) • ((n : ℝ)⁻¹ • ∑ i, f (y i) -
        (n : ℝ)⁻¹ • ∑ k ∈ range n, f (O k ω)))
      atTop (fun x ↦ x) (fun n ↦ resampleLaw O n ω)
      (multivariateGaussian 0 (covMatrix P fun i ω ↦ f (O 0 ω) i)) := by
  set S := covMatrix P fun i ω ↦ f (O 0 ω) i with hSdef
  have hc : ∀ i, MemLp (fun ω ↦ f (O 0 ω) i) 2 P := fun i ↦
    (EuclideanSpace.proj (𝕜 := ℝ) i).comp_memLp' hf2
  have hS : S.PosSemidef := posSemidef_covMatrix hc
  set m := P[fun ω ↦ f (O 0 ω)] with hm
  set C := ‖m‖ + 1 with hC
  set h : 𝒪 → ℝ := fun z ↦ ‖f z‖ + C with hh
  have hhm : Measurable h := by simp only [hh]; fun_prop
  have hh2 : Integrable (fun ω ↦ h (O 0 ω) ^ 2) P := by
    have h1 := (hf2.norm.add (memLp_const (μ := P) C))
    exact h1.integrable_sq
  have hmean := hO.tendsto_ae_smul_sum hf (hf2.integrable one_le_two)
  filter_upwards [hmean, ae_tendsto_inner_sq hO hf hf2, ae_tendsto_lindeberg hO hhm hh2]
    with ω hω1 hω2 hω3
  set xb : ℕ → EuclideanSpace ℝ ι := fun n ↦ (n : ℝ)⁻¹ • ∑ k ∈ range n, f (O k ω) with hxb
  have hxb' : Tendsto xb atTop (𝓝 m) := hω1
  have hsum : ∀ n : ℕ, 1 ≤ n → ∑ k ∈ range n, f (O k ω) = (n : ℝ) • xb n := fun n hn ↦ by
    have : (n : ℝ) ≠ 0 := by positivity
    simp only [hxb, smul_smul, mul_inv_cancel₀ this, one_smul]
  set g : ℕ → 𝒪 → EuclideanSpace ℝ ι := fun n z ↦ f z - xb n with hg
  have hgm : ∀ n, Measurable (g n) := fun n ↦ hf.sub_const _
  have h0 : ∀ᶠ n in atTop, ∑ k ∈ range n, g n (O k ω) = 0 := by
    filter_upwards [eventually_ge_atTop 1] with n hn
    simp only [hg, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, hsum n hn,
      ← Nat.cast_smul_eq_nsmul ℝ, sub_self]
  have hcov : ∀ t, Tendsto (fun n : ℕ ↦ (n : ℝ)⁻¹ * ∑ k ∈ range n, ⟪g n (O k ω), t⟫ ^ 2) atTop
      (𝓝 (WithLp.ofLp t ⬝ᵥ S *ᵥ WithLp.ofLp t)) := by
    intro t
    have hQ := hω2 t
    have hint : P[fun ω ↦ ⟪f (O 0 ω), t⟫] = ⟪m, t⟫ := by
      calc ∫ ω, ⟪f (O 0 ω), t⟫ ∂P = ∫ ω, ⟪t, f (O 0 ω)⟫ ∂P :=
            integral_congr_ae (ae_of_all _ fun ω ↦ real_inner_comm _ _)
        _ = ⟪t, m⟫ := integral_inner (hf2.integrable one_le_two) t
        _ = ⟪m, t⟫ := real_inner_comm _ _
    have hvar : WithLp.ofLp t ⬝ᵥ S *ᵥ WithLp.ofLp t =
        P[fun ω ↦ ⟪f (O 0 ω), t⟫ ^ 2] - ⟪m, t⟫ ^ 2 := by
      rw [hSdef, ← variance_inner_eq_covMatrix hf2 t, variance_eq_sub (hf2.inner_const t), hint]
      rfl
    have hxt : Tendsto (fun n ↦ ⟪xb n, t⟫) atTop (𝓝 ⟪m, t⟫) :=
      (continuous_id.inner continuous_const).continuousAt.tendsto.comp hxb'
    rw [hvar]
    refine (hQ.sub (hxt.pow 2)).congr' ((eventually_ge_atTop 1).mono fun n hn ↦ ?_)
    have hn0 : (n : ℝ) ≠ 0 := by positivity
    have hk : ∀ k, ⟪g n (O k ω), t⟫ ^ 2 =
        ⟪f (O k ω), t⟫ ^ 2 - 2 * ⟪xb n, t⟫ * ⟪f (O k ω), t⟫ + ⟪xb n, t⟫ ^ 2 :=
      fun k ↦ by simp only [hg, inner_sub_left]; ring
    have hlin : ∑ k ∈ range n, ⟪f (O k ω), t⟫ = n * ⟪xb n, t⟫ := by
      rw [← sum_inner, hsum n hn, inner_smul_left, conj_trivial]
    have e : ∑ k ∈ range n, ⟪g n (O k ω), t⟫ ^ 2 = ∑ k ∈ range n, ⟪f (O k ω), t⟫ ^ 2 -
        2 * ⟪xb n, t⟫ * ∑ k ∈ range n, ⟪f (O k ω), t⟫ + n * ⟪xb n, t⟫ ^ 2 := by
      simp only [hk, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
        Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    beta_reduce
    rw [e, hlin]
    field_simp
    ring
  have hL : ∀ ε, 0 < ε → Tendsto (fun n : ℕ ↦ (n : ℝ)⁻¹ * ∑ k ∈ range n,
      {x : ℝ | ε * √(n : ℝ) < |x|}.indicator (fun x ↦ x ^ 2) ‖g n (O k ω)‖) atTop (𝓝 0) := by
    intro ε hε
    have hclose : ∀ᶠ n in atTop, ‖xb n‖ ≤ C := by
      filter_upwards [hxb'.eventually (Metric.ball_mem_nhds m one_pos)] with n hn
      rw [dist_eq_norm] at hn
      have := norm_sub_norm_le (xb n) m
      simp only [hC]
      linarith
    refine squeeze_zero' (Eventually.of_forall fun n ↦ mul_nonneg
      (inv_nonneg.2 (Nat.cast_nonneg _))
      (Finset.sum_nonneg fun k _ ↦ Set.indicator_nonneg (fun _ _ ↦ sq_nonneg _) _))
      (hclose.mono fun n hn ↦ ?_) (hω3 ε hε)
    refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun k _ ↦ ?_)
      (inv_nonneg.2 (Nat.cast_nonneg _))
    refine indicator_sq_le_of_abs_le ?_ _
    have hC0 : 0 ≤ C := by positivity
    simp only [hg, hh]
    rw [abs_norm, abs_of_nonneg (by positivity : 0 ≤ ‖f (O k ω)‖ + C)]
    exact (norm_sub_le _ _).trans (by linarith)
  have hY : HasLaw (fun x : EuclideanSpace ℝ ι ↦ x) (multivariateGaussian 0 S)
      (multivariateGaussian 0 S) := ⟨aemeasurable_id, Measure.map_id⟩
  have hpath := tendstoInDistribution_resample_of_path_euclidean hgm h0 hS hcov hL hY
  refine tendstoInDistribution_congr_eventually hpath (Eventually.of_forall fun n ↦ ?_)
    fun n ↦ by
      have hs : Measurable fun y : Fin n → 𝒪 ↦ ∑ i, f (y i) :=
        Finset.measurable_fun_sum _ fun i _ ↦ hf.comp (measurable_pi_apply i)
      exact Measurable.aemeasurable (by fun_prop)
  funext y
  rw [sqrt_smul_inv_smul_sub]
  simp only [hg, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    ← Nat.cast_smul_eq_nsmul ℝ, hxb]

/-! ### Conditional weak convergence in probability and the delta method -/

/-- The vector mean `n⁻¹ • ∑_i f (y i)` of a resample `y` of size `n`. -/
noncomputable def resampleMeanVec {E : Type*} [AddCommGroup E] [Module ℝ E] (f : 𝒪 → E)
    (n : ℕ) (y : Fin n → 𝒪) : E :=
  (n : ℝ)⁻¹ • ∑ i, f (y i)

omit [Fintype ι] [DecidableEq ι] in
theorem measurable_resampleMeanVec [Finite ι] {f : 𝒪 → EuclideanSpace ℝ ι} (hf : Measurable f)
    (n : ℕ) : Measurable (resampleMeanVec f n) := by
  have := Fintype.ofFinite ι
  have hs : Measurable fun y : Fin n → 𝒪 ↦ ∑ i, f (y i) :=
    Finset.measurable_fun_sum _ fun i _ ↦ hf.comp (measurable_pi_apply i)
  unfold resampleMeanVec
  fun_prop

/-- **Conditional weak convergence in probability of the vector bootstrap mean.** Under the
hypotheses of `Bootstrap.ae_tendstoInDistribution_resampleMean_euclidean`, the bootstrap laws of
the vector resample mean satisfy the weak Bernstein and von Mises predicate with centering the
vector sample mean and limit `N(0, Σ)`. -/
theorem isBernsteinVonMisesWeak_resampleMeanVec {P : Measure Ω} [IsProbabilityMeasure P]
    {O : ℕ → Ω → 𝒪} (hO : IsIIDSample O P) {f : 𝒪 → EuclideanSpace ℝ ι} (hf : Measurable f)
    (hf2 : MemLp (fun ω ↦ f (O 0 ω)) 2 P) :
    IsBernsteinVonMisesWeak P (bootstrapLaw (resampleMeanVec f) O)
      (fun n ω ↦ (n : ℝ)⁻¹ • ∑ k ∈ range n, f (O k ω))
      (multivariateGaussian 0 (covMatrix P fun i ω ↦ f (O 0 ω) i)) := by
  refine ⟨fun _ _ ↦ inferInstance, inferInstance, fun φ hφc hφb ↦ ?_⟩
  obtain ⟨C, hC⟩ := hφb
  have hpre : ∀ (n : ℕ) ω, (n : ℝ)⁻¹ • ∑ k ∈ range n, f (O k ω) =
      resampleMeanVec f n (dataPrefix O n ω) := fun n ω ↦ by
    simp [resampleMeanVec, dataPrefix, Finset.sum_range]
  have hrw : ∀ (n : ℕ) ω, ∫ θ, φ (√(n : ℝ) • (θ - (n : ℝ)⁻¹ • ∑ k ∈ range n, f (O k ω)))
      ∂bootstrapLaw (resampleMeanVec f) O n ω =
      ∫ y, φ (√(n : ℝ) • (resampleMeanVec f n y - resampleMeanVec f n (dataPrefix O n ω)))
        ∂resampleLaw O n ω := by
    intro n ω
    rw [bootstrapLaw, integral_map (measurable_resampleMeanVec hf n).aemeasurable
      (f := fun θ ↦ φ (√(n : ℝ) • (θ - (n : ℝ)⁻¹ • ∑ k ∈ range n, f (O k ω))))
      (hφc.comp (by fun_prop : Continuous fun θ : EuclideanSpace ℝ ι ↦
        √(n : ℝ) • (θ - (n : ℝ)⁻¹ • ∑ k ∈ range n, f (O k ω)))).aestronglyMeasurable,
      hpre]
  simp only [hrw]
  have hmeas : ∀ n : ℕ, AEStronglyMeasurable (fun ω ↦ ∫ y,
      φ (√(n : ℝ) • (resampleMeanVec f n y - resampleMeanVec f n (dataPrefix O n ω)))
        ∂resampleLaw O n ω) P := by
    intro n
    have h1 : Measurable fun p : (Fin n → 𝒪) × (Fin n → 𝒪) ↦ resampleMeanVec f n p.2 :=
      (measurable_resampleMeanVec hf n).comp measurable_snd
    have h2 : Measurable fun p : (Fin n → 𝒪) × (Fin n → 𝒪) ↦ resampleMeanVec f n p.1 :=
      (measurable_resampleMeanVec hf n).comp measurable_fst
    have h3 : Measurable fun p : (Fin n → 𝒪) × (Fin n → 𝒪) ↦
        φ (√(n : ℝ) • (resampleMeanVec f n p.2 - resampleMeanVec f n p.1)) := by
      have := hφc.measurable
      fun_prop
    exact aestronglyMeasurable_integral_resampleLaw (fun k ↦ hO.aemeasurable k) n
      (H := fun x y ↦ φ (√(n : ℝ) • (resampleMeanVec f n y - resampleMeanVec f n x)))
      h3.stronglyMeasurable
  refine tendstoInMeasure_of_tendsto_ae hmeas ?_
  filter_upwards [ae_tendstoInDistribution_resampleMean_euclidean hO hf hf2] with ω hω
  set b : EuclideanSpace ℝ ι →ᵇ ℝ :=
    BoundedContinuousFunction.mkOfBound ⟨φ, hφc⟩ (2 * C) fun x y ↦ by
      rw [Real.dist_eq]
      simp only [ContinuousMap.coe_mk]
      rw [abs_le]
      constructor <;> linarith [abs_le.1 (hC x), abs_le.1 (hC y)]
  have h1 := (tendstoInDistribution_iff_forall_integral_rclike_tendsto ℝ
    hω.forall_aemeasurable aemeasurable_id).1 hω b
  simp only [b, BoundedContinuousFunction.mkOfBound_coe, ContinuousMap.coe_mk, id_eq] at h1
  refine h1.congr fun n ↦ ?_
  rw [← hpre]
  rfl

/-- **The bootstrap delta method: percentile coverage for a smooth function of a mean.** Let `O` be
an i.i.d. sample, `f : 𝒪 → ℝ^ι` measurable with `E‖f(O_0)‖² < ∞`, mean `m` and covariance `Σ`,
and let `Ψ : ℝ^ι → ℝ` be measurable and strictly differentiable at `m` with derivative `D`, with
`Var(D Z) > 0` for `Z ∼ N(0, Σ)`. For `α ∈ (0, 1)` and `Φ(z) = 1 - α/2`, the percentile interval
of the bootstrap law of `Ψ(X̄*_n)` covers `Ψ(m)` with probability tending to `1 - α`. -/
theorem tendsto_bootstrap_delta_coverage {P : Measure Ω} [IsProbabilityMeasure P]
    {O : ℕ → Ω → 𝒪} (hO : IsIIDSample O P) {f : 𝒪 → EuclideanSpace ℝ ι} (hf : Measurable f)
    (hf2 : MemLp (fun ω ↦ f (O 0 ω)) 2 P) {Ψ : EuclideanSpace ℝ ι → ℝ} (hΨm : Measurable Ψ)
    {D : EuclideanSpace ℝ ι →L[ℝ] ℝ} (hΨ : HasStrictFDerivAt Ψ D (P[fun ω ↦ f (O 0 ω)]))
    (hσ : 0 < Var[D; multivariateGaussian 0 (covMatrix P fun i ω ↦ f (O 0 ω) i)]) {α z : ℝ}
    (hα : α ∈ Set.Ioo (0 : ℝ) 1) (hz : cdf (gaussianReal 0 1) z = 1 - α / 2) :
    Tendsto (fun n ↦ P.real {ω | Ψ (P[fun ω ↦ f (O 0 ω)]) ∈
      Bootstrap.percentileInterval ((bootstrapLaw (resampleMeanVec f) O n ω).map Ψ) α}) atTop
      (𝓝 (1 - α)) := by
  set N := multivariateGaussian 0 (covMatrix P fun i ω ↦ f (O 0 ω) i)
  have hY : HasLaw (fun x : EuclideanSpace ℝ ι ↦ x) N N := ⟨aemeasurable_id, Measure.map_id⟩
  have hT := hO.tendstoInDistribution_multivariateGaussian hf hf2 hY
  have hN0 : ∫ x, x ∂N = 0 := integral_id_multivariateGaussian
  exact (isBernsteinVonMisesWeak_resampleMeanVec hO hf hf2).tendsto_credibleInterval_coverage_map
    hN0 hY hT hΨm hΨ hσ hα hz

end Bootstrap

end CausalInference
