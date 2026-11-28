/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.Estimation.MaximumLikelihoodNormalityVector
public import CausalInference.Estimation.ChiSquared

/-!
# The Wald, score and likelihood ratio tests for a vector parameter

For a parameter `θ ∈ ℝ^p` and an i.i.d. sample of size `n` from `P_θ₀`, the three classical
statistics for the null hypothesis `θ = θ₀` are

* the Wald statistic `W_n = n (θ̂_n - θ₀)ᵀ Î_n (θ̂_n - θ₀)`, with `Î_n` the information matrix
  `I(θ₀)` or any consistent estimate of it;
* the score statistic `R_n = Z_nᵀ I(θ₀)⁻¹ Z_n`, `Z_n = n^{-1/2} ∑_{i < n} s(θ₀; O_i)`;
* the likelihood ratio statistic `Λ_n = 2 ∑_{i < n} (ℓ(θ̂_n; O_i) - ℓ(θ₀; O_i))`.

Under the null each converges in distribution to the chi-square law with `p` degrees of freedom
(`CausalInference.chiSquared`), and the three are asymptotically equivalent: `Λ_n - W_n` and
`R_n - W_n` tend to zero in probability. The likelihood ratio statistic is handled by a second
order expansion of the log-likelihood along the segment from `θ̂_n` (where the score vanishes)
to `θ₀`, with the average Hessian close to `-I(θ₀)` near `θ₀` by the uniform law of large
numbers.

## Main definitions

* `CausalInference.waldStatVec`, `CausalInference.ParametricFamily.scoreStatVec`,
  `CausalInference.ParametricFamily.lrStatVec`.

## Main results

* `CausalInference.waldStatVec_tendstoInDistribution`: the Wald test, with known or consistently
  estimated information.
* `CausalInference.ParametricFamily.scoreStatVec_tendstoInDistribution`: the score test.
* `CausalInference.ParametricFamily.scoreStatVec_sub_waldStatVec_tendstoInMeasure` and
  `lrStatVec_sub_waldStatVec_tendstoInMeasure`: asymptotic equivalence.
* `CausalInference.ParametricFamily.lrStatVec_tendstoInDistribution`: **Wilks' theorem** for a
  vector parameter.

References: S. S. Wilks (1938), *The large-sample distribution of the likelihood ratio for
testing composite hypotheses*, Annals of Mathematical Statistics; A. Wald (1943), *Tests of
statistical hypotheses concerning several parameters when the number of observations is large*,
Transactions of the American Mathematical Society; C. R. Rao (1948), *Large sample tests of
statistical hypotheses concerning several parameters with applications to problems of
estimation*, Proceedings of the Cambridge Philosophical Society; A. W. van der Vaart (1998),
*Asymptotic Statistics*, chapter 16.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Finset Metric Matrix
open scoped Topology ENNReal NNReal RealInnerProductSpace

namespace CausalInference

open BiasAnalysis.MeasurementError (covMatrix)

variable {p : ℕ}

/-! ### Quadratic forms -/

/-- The Euclidean vector `√n (a - b)` in coordinates. -/
lemma ofLp_sqrt_smul_sub (n : ℕ) (a b : Fin p → ℝ) :
    WithLp.ofLp (√(n : ℝ) • (WithLp.toLp 2 a - WithLp.toLp 2 b : EuclideanSpace ℝ (Fin p))) =
      √(n : ℝ) • (a - b) := rfl

/-- A bilinear value of a matrix is bounded through the operator norm:
`|xᵀ A y| ≤ ‖x‖ ‖A‖ ‖y‖`. -/
theorem abs_dotProduct_mulVec_le (A : Matrix (Fin p) (Fin p) ℝ)
    (x y : EuclideanSpace ℝ (Fin p)) :
    |WithLp.ofLp x ⬝ᵥ A *ᵥ WithLp.ofLp y| ≤ ‖x‖ * (‖matrixCLM A‖ * ‖y‖) := by
  have e : WithLp.ofLp x ⬝ᵥ A *ᵥ WithLp.ofLp y = ⟪matrixCLM A y, x⟫ := by
    rw [EuclideanSpace.inner_eq_star_dotProduct, matrixCLM_apply]
    simp
  rw [e, mul_comm ‖x‖]
  exact (abs_real_inner_le_norm _ _).trans
    (mul_le_mul_of_nonneg_right ((matrixCLM A).le_opNorm y) (norm_nonneg x))

/-- The difference of two values of a symmetric quadratic form:
`vᵀ A v - wᵀ A w = (v - w)ᵀ A (v + w)`. -/
theorem dotProduct_mulVec_sub_dotProduct_mulVec {A : Matrix (Fin p) (Fin p) ℝ} (hA : Aᵀ = A)
    (v w : Fin p → ℝ) :
    v ⬝ᵥ A *ᵥ v - w ⬝ᵥ A *ᵥ w = (v - w) ⬝ᵥ A *ᵥ (v + w) := by
  have hs : v ⬝ᵥ A *ᵥ w = w ⬝ᵥ A *ᵥ v := by
    rw [dotProduct_mulVec, ← mulVec_transpose, hA, dotProduct_comm]
  rw [mulVec_add, dotProduct_add, sub_dotProduct, sub_dotProduct, hs]
  ring

/-- `|vᵀ A v| ≤ p² ‖A‖ ‖v‖²` for an array `A` and a vector `v` with sup norms. -/
theorem abs_dotProduct_of_mulVec_le (A : Fin p → Fin p → ℝ) (v : Fin p → ℝ) :
    |v ⬝ᵥ Matrix.of A *ᵥ v| ≤ (p : ℝ) ^ 2 * ‖A‖ * ‖v‖ ^ 2 := by
  have hv : ∀ i, |v i| ≤ ‖v‖ := fun i ↦ by
    rw [← Real.norm_eq_abs]; exact norm_le_pi_norm v i
  have hA : ∀ i j, |A i j| ≤ ‖A‖ := fun i j ↦ by
    rw [← Real.norm_eq_abs]
    exact (norm_le_pi_norm (A i) j).trans (norm_le_pi_norm A i)
  calc |v ⬝ᵥ Matrix.of A *ᵥ v| = |∑ i, ∑ j, v i * (A i j * v j)| := by
        simp [dotProduct, mulVec, Finset.mul_sum]
    _ ≤ ∑ i : Fin p, ∑ j : Fin p, ‖v‖ * (‖A‖ * ‖v‖) := by
        refine (abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ ↦ ?_)
        refine (abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ ↦ ?_)
        rw [abs_mul, abs_mul]
        exact mul_le_mul (hv i) (mul_le_mul (hA i j) (hv j) (abs_nonneg _) (norm_nonneg _))
          (by positivity) (norm_nonneg _)
    _ = (p : ℝ) ^ 2 * ‖A‖ * ‖v‖ ^ 2 := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        ring

/-- A sequence dominated in absolute value by a sequence tending to zero in probability tends
to zero in probability. -/
theorem tendstoInMeasure_zero_of_abs_le {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    {X V : ℕ → Ω → ℝ} (hV : TendstoInMeasure μ V atTop 0) (h : ∀ n ω, |X n ω| ≤ |V n ω|) :
    TendstoInMeasure μ X atTop 0 := by
  rw [tendstoInMeasure_iff_dist] at hV ⊢
  intro ε hε
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds (hV ε hε)
    (fun _ ↦ zero_le) fun n ↦ measure_mono fun ω hω ↦ ?_
  simp only [Set.mem_ofPred_eq, Pi.zero_apply, Real.dist_eq, sub_zero] at hω ⊢
  exact hω.trans (h n ω)

/-! ### The Wald test -/

section Wald

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- The Wald statistic `n (θ̂_n - θ₀)ᵀ Î_n (θ̂_n - θ₀)` for the null `θ = θ₀`, with information
matrix `Î_n`. -/
noncomputable def waldStatVec (θh : ℕ → Ω → Fin p → ℝ) (θ₀ : Fin p → ℝ)
    (Ih : ℕ → Ω → Matrix (Fin p) (Fin p) ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  n * ((θh n ω - θ₀) ⬝ᵥ Ih n ω *ᵥ (θh n ω - θ₀))

omit [IsProbabilityMeasure μ] in
/-- The Wald statistic is the quadratic form of `Î_n` at `√n (θ̂_n - θ₀)`. -/
theorem waldStatVec_eq_quadForm (θh : ℕ → Ω → Fin p → ℝ) (θ₀ : Fin p → ℝ)
    (Ih : ℕ → Ω → Matrix (Fin p) (Fin p) ℝ) (n : ℕ) (ω : Ω) :
    waldStatVec θh θ₀ Ih n ω = quadForm (Ih n ω)
      (√(n : ℝ) • (WithLp.toLp 2 (θh n ω) - WithLp.toLp 2 θ₀ : EuclideanSpace ℝ (Fin p))) := by
  rw [quadForm_smul, Real.sq_sqrt (Nat.cast_nonneg n)]
  rfl

/-- **The Wald test.** If `√n (θ̂_n - θ₀)` converges in distribution to `N(0, I⁻¹)` with `I`
positive definite and `Î_n → I` entrywise in probability (`Î_n = I` for the known information),
then `W_n = n (θ̂_n - θ₀)ᵀ Î_n (θ̂_n - θ₀)` converges in distribution to every variable with law
`χ²_p`. -/
theorem waldStatVec_tendstoInDistribution {θh : ℕ → Ω → Fin p → ℝ} {θ₀ : Fin p → ℝ}
    {I : Matrix (Fin p) (Fin p) ℝ} (hI : I.PosDef)
    {Ω' : Type*} {mΩ' : MeasurableSpace Ω'} {P' : Measure Ω'} [IsProbabilityMeasure P']
    {Y : Ω' → EuclideanSpace ℝ (Fin p)} (hY : HasLaw Y (multivariateGaussian 0 I⁻¹) P')
    (hN : TendstoInDistribution (fun (n : ℕ) ω ↦
      √(n : ℝ) • (WithLp.toLp 2 (θh n ω) - WithLp.toLp 2 θ₀ : EuclideanSpace ℝ (Fin p))) atTop Y
      (fun _ ↦ μ) P')
    {Ih : ℕ → Ω → Matrix (Fin p) (Fin p) ℝ}
    (hIh : ∀ j k, TendstoInMeasure μ (fun n ω ↦ Ih n ω j k) atTop (fun _ ↦ I j k))
    (hIhm : ∀ n j k, AEMeasurable (fun ω ↦ Ih n ω j k) μ)
    {Ω'' : Type*} {mΩ'' : MeasurableSpace Ω''} {P'' : Measure Ω''} [IsProbabilityMeasure P'']
    {W : Ω'' → ℝ} (hW : HasLaw W (chiSquared p) P'') :
    TendstoInDistribution (waldStatVec θh θ₀ Ih) atTop W (fun _ ↦ μ) P'' := by
  have hC' : TendstoInMeasure μ (fun n ω ↦ (fun j k ↦ Ih n ω j k : Fin p → Fin p → ℝ)) atTop
      (fun _ ↦ (fun j k ↦ I j k : Fin p → Fin p → ℝ)) :=
    tendstoInMeasure_pi (X := fun j n ω k ↦ Ih n ω j k) fun j ↦
      tendstoInMeasure_pi (X := fun k n ω ↦ Ih n ω j k) fun k ↦ hIh j k
  have hCm : ∀ n, AEMeasurable (fun ω ↦ (fun j k ↦ Ih n ω j k : Fin p → Fin p → ℝ)) μ :=
    fun n ↦ AEMeasurable.of_eval fun j ↦ AEMeasurable.of_eval fun k ↦ hIhm n j k
  have hc := PiLp.continuous_ofLp 2 (fun _ : Fin p ↦ ℝ)
  have hg : Continuous fun q : EuclideanSpace ℝ (Fin p) × (Fin p → Fin p → ℝ) ↦
      quadForm (Matrix.of q.2) q.1 :=
    (hc.comp continuous_fst).dotProduct
      (Continuous.matrix_mulVec continuous_snd (hc.comp continuous_fst))
  have h := hN.continuous_comp_prodMk_of_tendstoInMeasure_const hg hC' hCm
  have hlaw := hY.quadForm_chiSquared_of_inv hI
  convert h.of_hasLaw hlaw hW using 1
  funext n ω
  rw [waldStatVec_eq_quadForm]
  rfl

end Wald

namespace ParametricFamily

variable {S : Type*} [MeasurableSpace S] {F : ParametricFamily (Fin p → ℝ) S} {Ω : Type*}
  {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ] {O : ℕ → Ω → S}
  {θ₀ : Fin p → ℝ}

/-! ### The score test -/

/-- The score statistic `Z_nᵀ I(θ₀)⁻¹ Z_n` with `Z_n = n^{-1/2} ∑_{i < n} s(θ₀; O_i)`. -/
noncomputable def scoreStatVec (F : ParametricFamily (Fin p → ℝ) S) (O : ℕ → Ω → S)
    (θ₀ : Fin p → ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  quadForm (F.fisherInfoMatrix θ₀)⁻¹
    ((√(n : ℝ))⁻¹ • ∑ i ∈ range n, F.scoreVecE (O i ω) (WithLp.toLp 2 θ₀))

/-- The likelihood ratio statistic `2 ∑_{i < n} (ℓ(θ̂_n; O_i) - ℓ(θ₀; O_i))`. -/
noncomputable def lrStatVec (F : ParametricFamily (Fin p → ℝ) S) (O : ℕ → Ω → S)
    (θh : ℕ → Ω → Fin p → ℝ) (θ₀ : Fin p → ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  2 * ∑ i ∈ range n, (F.logLik (θh n ω) (O i ω) - F.logLik θ₀ (O i ω))

/-- At a regular point with measurable score, the Euclidean score of an observation with law
`P_θ₀` is square integrable with mean zero. -/
theorem memLp_scoreVecE (hO : IsIIDSample O μ) (hlaw : μ.map (O 0) = F.law θ₀)
    (hreg : F.IsRegularAtVec θ₀) (hm : Measurable (F.scoreVec θ₀)) :
    MemLp (fun ω ↦ F.scoreVecE (O 0 ω) (WithLp.toLp 2 θ₀)) 2 μ ∧
      μ[fun ω ↦ F.scoreVecE (O 0 ω) (WithLp.toLp 2 θ₀)] = 0 := by
  have hX := hO.aemeasurable 0
  have hcomp : ∀ k, Measurable fun x ↦ F.scoreVec θ₀ x k := fun k ↦
    (measurable_pi_apply k).comp hm
  have hmk : ∀ k, MemLp (fun ω ↦ F.scoreVec θ₀ (O 0 ω) k) 2 μ := fun k ↦
    (memLp_map_measure_iff (hcomp k).aestronglyMeasurable hX).1
      (by rw [hlaw]; exact hreg.memLp_scoreVec k)
  have hB : MemLp (fun ω ↦ F.scoreVecE (O 0 ω) (WithLp.toLp 2 θ₀)) 2 μ := memLp_piLp_iff.2 hmk
  refine ⟨hB, ?_⟩
  ext k
  rw [eval_integral_piLp (fun j ↦ (hB.integrable one_le_two).eval_piLp j)]
  change ∫ ω, F.scoreVec θ₀ (O 0 ω) k ∂μ = 0
  rw [← integral_map hX (hcomp k).aestronglyMeasurable, hlaw,
    integral_scoreVec_eq_zero hreg.mem_nhds hreg.interchange.1.self_of_nhds k]

/-- **The central limit theorem for the score vector**: at a regular point with measurable score,
for observations with law `P_θ₀`, `n^{-1/2} ∑_{i < n} s(θ₀; O_i)` converges in distribution to
`N(0, I(θ₀))`. -/
theorem sum_scoreVecE_tendstoInDistribution (hO : IsIIDSample O μ)
    (hlaw : μ.map (O 0) = F.law θ₀) (hreg : F.IsRegularAtVec θ₀) (hm : Measurable (F.scoreVec θ₀))
    {Ω' : Type*} {mΩ' : MeasurableSpace Ω'} {P' : Measure Ω'} [IsProbabilityMeasure P']
    {Y : Ω' → EuclideanSpace ℝ (Fin p)}
    (hY : HasLaw Y (multivariateGaussian 0 (F.fisherInfoMatrix θ₀)) P') :
    TendstoInDistribution (fun (n : ℕ) ω ↦
      (√(n : ℝ))⁻¹ • ∑ i ∈ range n, F.scoreVecE (O i ω) (WithLp.toLp 2 θ₀)) atTop Y
      (fun _ ↦ μ) P' := by
  obtain ⟨hB, hzero⟩ := memLp_scoreVecE hO hlaw hreg hm
  have hψm : Measurable fun z ↦ F.scoreVecE z (WithLp.toLp 2 θ₀) :=
    (PiLp.continuous_toLp 2 _).measurable.comp hm
  have hcov : covMatrix μ (fun i ω ↦ F.scoreVecE (O 0 ω) (WithLp.toLp 2 θ₀) i) =
      F.fisherInfoMatrix θ₀ := by
    rw [covMatrix_eq_meatMatrix hO hψm hB hzero, hlaw, meatMatrix_scoreVec_eq_fisherInfoMatrix]
  rw [← hcov] at hY
  have h := hO.tendstoInDistribution_multivariateGaussian hψm hB hY
  simp only [hzero, sub_zero, smul_smul, sqrt_mul_inv_self] at h
  exact h

/-- **The score test.** At a regular point with measurable score and positive definite
information, for observations with law `P_θ₀`, the score statistic converges in distribution to
every variable with law `χ²_p`. No estimator is involved. -/
theorem scoreStatVec_tendstoInDistribution (hO : IsIIDSample O μ)
    (hlaw : μ.map (O 0) = F.law θ₀) (hreg : F.IsRegularAtVec θ₀) (hm : Measurable (F.scoreVec θ₀))
    (hI : (F.fisherInfoMatrix θ₀).PosDef)
    {Ω'' : Type*} {mΩ'' : MeasurableSpace Ω''} {P'' : Measure Ω''} [IsProbabilityMeasure P'']
    {W : Ω'' → ℝ} (hW : HasLaw W (chiSquared p) P'') :
    TendstoInDistribution (F.scoreStatVec O θ₀) atTop W (fun _ ↦ μ) P'' := by
  have h0 := sum_scoreVecE_tendstoInDistribution hO hlaw hreg hm
    (P' := multivariateGaussian 0 (F.fisherInfoMatrix θ₀)) (Y := id) HasLaw.id
  have h := h0.continuous_comp (continuous_quadForm (F.fisherInfoMatrix θ₀)⁻¹)
  exact h.of_hasLaw (HasLaw.id.quadForm_inv_chiSquared hI) hW

/-! ### Asymptotic equivalence of the score and Wald statistics -/

/-- `√n (n⁻¹ x) = (√n)⁻¹ x`. -/
lemma sqrt_smul_inv_smul {E : Type*} [AddCommGroup E] [Module ℝ E] (n : ℕ) (x : E) :
    √(n : ℝ) • ((n : ℝ)⁻¹ • x) = (√(n : ℝ))⁻¹ • x := by
  rw [smul_smul, sqrt_mul_inv_self]

/-- **The score and Wald statistics are asymptotically equivalent.** Under the hypotheses of
`mle_tendstoInDistribution_vec` (measurability of `θh n` is not needed),
`R_n - n (θ̂_n - θ₀)ᵀ I(θ₀) (θ̂_n - θ₀) → 0` in probability. With `Y_n = √n (θ̂_n - θ₀)`,
`Z_n = n^{-1/2} ∑ s(θ₀; O_i)` and `b_n = I⁻¹ Z_n`, `R_n = b_nᵀ I b_n`, so the difference is
`-(Y_n - b_n)ᵀ I (Y_n + b_n)`, with `Y_n - b_n → 0` by the linear expansion and `b_n` bounded in
probability by the central limit theorem. -/
theorem scoreStatVec_sub_waldStatVec_tendstoInMeasure (hO : IsIIDSample O μ)
    (hlaw : μ.map (O 0) = F.law θ₀) (hreg : F.IsRegularAtVec θ₀) {r : ℝ}
    (hs : F.IsScoreRegularVec θ₀ r) (hI : (F.fisherInfoMatrix θ₀).PosDef)
    {θh : ℕ → Ω → Fin p → ℝ} (hθ : TendstoInMeasure μ θh atTop (fun _ ↦ θ₀))
    (hroot : WithProbTendingToOne μ
      (fun n ↦ {ω | ∑ i ∈ range n, F.scoreVec (θh n ω) (O i ω) = 0})) :
    TendstoInMeasure μ (F.scoreStatVec O θ₀ -
      waldStatVec θh θ₀ (fun _ _ ↦ F.fisherInfoMatrix θ₀)) atTop 0 := by
  set I := F.fisherInfoMatrix θ₀
  obtain ⟨hψm, hJm, hderiv, hcont, ⟨H, hH, hdom⟩, hzero, hB⟩ :=
    zEstimator_hypotheses_scoreVecE hO hlaw hreg hs
  have hbread : breadMatrix (μ.map (O 0)) F.scoreJacobianE (WithLp.toLp 2 θ₀) = I := by
    rw [hlaw, breadMatrix_scoreVec_eq_fisherInfoMatrix hreg]
  have hA : (breadMatrix (μ.map (O 0)) F.scoreJacobianE (WithLp.toLp 2 θ₀)).det ≠ 0 := by
    rw [hbread]; exact hI.det_pos.ne'
  have hdiff := vectorZEstimator_tendstoInMeasure_sub hO hs.pos hψm hJm hderiv hcont hH hdom
    hzero hB hA (θh := fun n ω ↦ WithLp.toLp 2 (θh n ω))
    (hθ.comp_continuousAt (PiLp.continuous_toLp 2 _).continuousAt)
    (tendstoInMeasure_sqrt_smul_scoreVecE hroot)
  rw [hbread] at hdiff
  set Y : ℕ → Ω → EuclideanSpace ℝ (Fin p) := fun n ω ↦
    √(n : ℝ) • (WithLp.toLp 2 (θh n ω) - WithLp.toLp 2 θ₀) with hYdef
  set Z : ℕ → Ω → EuclideanSpace ℝ (Fin p) := fun n ω ↦
    (√(n : ℝ))⁻¹ • ∑ i ∈ range n, F.scoreVecE (O i ω) (WithLp.toLp 2 θ₀) with hZdef
  set L := Matrix.toEuclideanCLM (𝕜 := ℝ) I⁻¹
  have hD : TendstoInMeasure μ (fun n ω ↦ ‖Y n ω - L (Z n ω)‖) atTop (fun _ ↦ 0) := by
    have h := hdiff.comp_continuousAt (g := fun v ↦ ‖v‖) continuous_norm.continuousAt
    simp only [norm_zero, sqrt_smul_inv_smul] at h
    exact h
  have hD0 : TendstoInMeasure μ (fun n ω ↦ ‖Y n ω - L (Z n ω)‖) atTop 0 := hD
  have hb : BoundedInProbability μ (fun n ω ↦ ‖L (Z n ω)‖) := by
    have h := ((sum_scoreVecE_tendstoInDistribution hO hlaw hreg hs.measurable_scoreVec
      (P' := multivariateGaussian 0 I) (Y := id) HasLaw.id).continuous_comp
      L.continuous).boundedInProbability
    intro κ hκ
    obtain ⟨M, hM, hev⟩ := h κ hκ
    exact ⟨M, hM, hev⟩
  have hBd : BoundedInProbability μ (fun n ω ↦ ‖matrixCLM I‖ *
      (‖Y n ω - L (Z n ω)‖ + 2 * ‖L (Z n ω)‖)) :=
    (((boundedInProbability_of_tendstoInMeasure hD0).add
      (hb.const_mul (c := fun _ ↦ 2) (B := 2) (Eventually.of_forall fun _ ↦ by norm_num))).const_mul
      (c := fun _ ↦ ‖matrixCLM I‖) (B := ‖matrixCLM I‖)
      (Eventually.of_forall fun _ ↦ (abs_of_nonneg (norm_nonneg _)).le))
  have hprod := tendstoInMeasure_mul_of_bounded hD0 hBd
  refine tendstoInMeasure_zero_of_abs_le hprod fun n ω ↦ ?_
  have hIt : Iᵀ = I := fisherInfoMatrix_transpose θ₀
  have hIu : IsUnit I.det := isUnit_iff_ne_zero.2 hI.det_pos.ne'
  have hR : F.scoreStatVec O θ₀ n ω = quadForm I (L (Z n ω)) := by
    change quadForm I⁻¹ (Z n ω) = quadForm I (WithLp.toLp 2 (I⁻¹ *ᵥ WithLp.ofLp (Z n ω)))
    rw [quadForm, quadForm, WithLp.ofLp_toLp, mulVec_mulVec, mul_nonsing_inv _ hIu, one_mulVec]
    exact dotProduct_comm _ _
  have hW : waldStatVec θh θ₀ (fun _ _ ↦ I) n ω = quadForm I (Y n ω) :=
    waldStatVec_eq_quadForm _ _ _ n ω
  change |F.scoreStatVec O θ₀ n ω - waldStatVec θh θ₀ (fun _ _ ↦ I) n ω| ≤ _
  rw [hR, hW, abs_sub_comm, quadForm, quadForm, dotProduct_mulVec_sub_dotProduct_mulVec hIt,
    ← WithLp.ofLp_sub, ← WithLp.ofLp_add]
  refine (abs_dotProduct_mulVec_le I _ _).trans ?_
  have hsum : ‖Y n ω + L (Z n ω)‖ ≤ ‖Y n ω - L (Z n ω)‖ + 2 * ‖L (Z n ω)‖ := by
    calc ‖Y n ω + L (Z n ω)‖ = ‖(Y n ω - L (Z n ω)) + 2 • L (Z n ω)‖ := by
          congr 1; rw [two_smul]; abel
      _ ≤ ‖Y n ω - L (Z n ω)‖ + ‖(2 : ℝ) • L (Z n ω)‖ := by
          rw [← ofNat_smul_eq_nsmul ℝ 2]; exact norm_add_le _ _
      _ = ‖Y n ω - L (Z n ω)‖ + 2 * ‖L (Z n ω)‖ := by rw [norm_smul]; norm_num
  have hnn : 0 ≤ ‖Y n ω - L (Z n ω)‖ * (‖matrixCLM I‖ *
      (‖Y n ω - L (Z n ω)‖ + 2 * ‖L (Z n ω)‖)) := by positivity
  rw [abs_of_nonneg hnn]
  gcongr

/-! ### Wilks' theorem -/

/-- The sup norm of a vector is at most its Euclidean norm. -/
lemma norm_sub_le_norm_toLp_sub (v w : Fin p → ℝ) :
    ‖v - w‖ ≤ ‖(WithLp.toLp 2 v - WithLp.toLp 2 w : EuclideanSpace ℝ (Fin p))‖ :=
  (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun i ↦
    PiLp.norm_apply_le (WithLp.toLp 2 v - WithLp.toLp 2 w : EuclideanSpace ℝ (Fin p)) i

/-- **The likelihood ratio and Wald statistics are asymptotically equivalent.** Under the
hypotheses of `mle_tendstoInDistribution_vec`,
`Λ_n - n (θ̂_n - θ₀)ᵀ I(θ₀) (θ̂_n - θ₀) → 0` in probability. Along the segment
`u_t = θ̂_n + t (θ₀ - θ̂_n)`, `t ∈ [0, 1]`, the log-likelihood has first derivative zero at
`t = 0` (the score equations) and second derivative `dᵀ (∑ ∂s(u_t; O_i)) d`, `d = θ₀ - θ̂_n`,
which is within `η n ‖d‖²` of `-n dᵀ I(θ₀) d` with probability tending to one, by the uniform
law of large numbers for the Hessian on the closed ball and its continuity at `θ₀`
(`abs_sub_sub_le_of_hasDerivAt_two`); `n ‖θ̂_n - θ₀‖²` is bounded in probability. -/
theorem lrStatVec_sub_waldStatVec_tendstoInMeasure (hO : IsIIDSample O μ)
    (hlaw : μ.map (O 0) = F.law θ₀) (hreg : F.IsRegularAtVec θ₀) {r : ℝ}
    (hs : F.IsScoreRegularVec θ₀ r) (hI : (F.fisherInfoMatrix θ₀).PosDef)
    {θh : ℕ → Ω → Fin p → ℝ} (hθm : ∀ n, AEMeasurable (θh n) μ)
    (hθ : TendstoInMeasure μ θh atTop (fun _ ↦ θ₀))
    (hroot : WithProbTendingToOne μ
      (fun n ↦ {ω | ∑ i ∈ range n, F.scoreVec (θh n ω) (O i ω) = 0})) :
    TendstoInMeasure μ (F.lrStatVec O θh θ₀ -
      waldStatVec θh θ₀ (fun _ _ ↦ F.fisherInfoMatrix θ₀)) atTop 0 := by
  set I := F.fisherInfoMatrix θ₀
  have hN := mle_tendstoInDistribution_vec hO hlaw hreg hs hI hθm hθ hroot
    (P' := multivariateGaussian 0 I⁻¹) (Y := id) HasLaw.id
  set ψ : S → (Fin p → ℝ) → Fin p → Fin p → ℝ := fun z u i j ↦ F.hessianLogLik j i u z
    with hψ
  obtain ⟨H, hH, hdom⟩ := hs.dominated
  obtain ⟨hMc, hunif⟩ := uniform_law_of_large_numbers hO (isCompact_closedBall θ₀ r) (ψ := ψ)
    (fun u hu ↦ Measurable.of_eval fun i ↦ Measurable.of_eval fun j ↦
      hs.measurable_hessianLogLik u hu j i)
    (by
      rw [hlaw]
      filter_upwards [hs.continuousOn_hessianLogLik] with z hz using
        continuousOn_pi.2 fun i ↦ continuousOn_pi.2 fun j ↦ hz j i)
    (H := fun z ↦ |H z|) (by rw [hlaw]; exact hH.abs)
    (by
      rw [hlaw]
      filter_upwards [hdom] with z hz u hu using
        (pi_norm_le_iff_of_nonneg (abs_nonneg _)).2 fun i ↦
          (pi_norm_le_iff_of_nonneg (abs_nonneg _)).2 fun j ↦ by
            rw [Real.norm_eq_abs]; exact (hz u hu j i).trans (le_abs_self _))
  generalize hMdef : (fun u ↦ ∫ z, ψ z u ∂(μ.map (O 0))) = M at hMc hunif
  have hMI : Matrix.of (M θ₀) = -I := by
    ext i j
    have hint : ∀ i j, Integrable (fun z ↦ ψ z θ₀ i j) (F.law θ₀) := fun i j ↦
      (hreg.information_equality j i).2.1
    have hsym : I j i = I i j := by
      rw [← transpose_apply I i j, fisherInfoMatrix_transpose θ₀]
    rw [of_apply, Matrix.neg_apply, ← hMdef, hlaw]
    change (∫ z, ψ z θ₀ ∂F.law θ₀) i j = -I i j
    rw [eval_integral (fun i ↦ Integrable.of_eval (hint i)) i, eval_integral (hint i) j, ← hsym]
    have heq : I j i = -∫ x, F.hessianLogLik j i θ₀ x ∂F.law θ₀ :=
      (hreg.information_equality j i).2.2
    rw [heq, neg_neg]
  have hMat : ContinuousAt M θ₀ := hMc.continuousAt (closedBall_mem_nhds θ₀ hs.pos)
  have hboth : ∀ᵐ z ∂(μ.map (O 0)), ∀ u ∈ closedBall θ₀ r,
      HasFDerivAt (fun v ↦ F.logLik v z) (gradCLM (F.scoreVec u z)) u ∧
        HasFDerivAt (fun v ↦ F.scoreVec v z) (mulVecCLM (F.scoreJacobian u z)) u := by
    rw [hlaw]
    filter_upwards [hs.hasFDerivAt_logLik, hs.hasFDerivAt_scoreVec] with z h1 h2 u hu using
      ⟨h1 u hu, h2 u hu⟩
  have hXb := hN.boundedInProbability
  refine tendstoInMeasure_zero_of_abs_le_mul_sq
    (X := fun (n : ℕ) ω ↦ ‖√(n : ℝ) • (WithLp.toLp 2 (θh n ω) - WithLp.toLp 2 θ₀ :
      EuclideanSpace ℝ (Fin p))‖) (fun κ hκ ↦ ?_) fun η hη ↦ ?_
  · obtain ⟨C, hC, hev⟩ := hXb κ hκ
    exact ⟨C, hC, by simpa only [norm_norm] using hev⟩
  set η' := η / (2 * ((p : ℝ) ^ 2 + 1)) with hη'
  have hη'pos : 0 < η' := by positivity
  obtain ⟨δ, hδ, hMδ⟩ := Metric.continuousAt_iff.1 hMat (η' / 2) (by positivity)
  have hδr : 0 < min δ r := lt_min hδ hs.pos
  refine ((((hθ.withProbTendingToOne_dist_lt hδr).inter (hunif (η' / 2) (by positivity))).inter
    (WithProbTendingToOne.of_ae (hO.ae_forall hboth))).inter hroot).mono fun n ω hω ↦ ?_
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := hω
  simp only [Set.mem_ofPred_eq] at h1 h2 h3 h4 ⊢
  set a := θh n ω with ha
  set d := θ₀ - a with hd
  set u : ℝ → Fin p → ℝ := fun t ↦ a + t • d with hu
  have hmem : ∀ t ∈ Set.uIcc (0 : ℝ) 1, dist (u t) θ₀ < min δ r := fun t ht ↦ by
    rw [Set.uIcc_of_le zero_le_one] at ht
    have e : u t - θ₀ = (1 - t) • (a - θ₀) := by simp only [hu, hd]; module
    rw [dist_eq_norm, e, norm_smul, Real.norm_eq_abs, abs_of_nonneg (by linarith [ht.2])]
    calc (1 - t) * ‖a - θ₀‖ ≤ 1 * ‖a - θ₀‖ := by gcongr; linarith [ht.1]
      _ = dist a θ₀ := by rw [one_mul, dist_eq_norm]
      _ < min δ r := h1
  have hball : ∀ t ∈ Set.uIcc (0 : ℝ) 1, u t ∈ closedBall θ₀ r := fun t ht ↦
    mem_closedBall.2 ((hmem t ht).le.trans (min_le_right _ _))
  have hline : ∀ t, HasDerivAt u d t := fun t ↦
    (((hasDerivAt_id t).smul_const d).const_add a).congr_deriv (one_smul ℝ d)
  set Q : (Fin p → Fin p → ℝ) → ℝ := fun A ↦ d ⬝ᵥ Matrix.of A *ᵥ d with hQ
  have hQsub : ∀ A B, Q (A - B) = Q A - Q B := fun A B ↦ by
    change d ⬝ᵥ (Matrix.of A - Matrix.of B) *ᵥ d = _
    rw [sub_mulVec, dotProduct_sub]
  have hQsmul : ∀ (c : ℝ) A, Q (c • A) = c * Q A := fun c A ↦ by
    change d ⬝ᵥ (c • Matrix.of A) *ᵥ d = _
    rw [smul_mulVec, dotProduct_smul, smul_eq_mul]
  have hQsum : ∀ (s : Finset ℕ) (A : ℕ → Fin p → Fin p → ℝ),
      Q (∑ i ∈ s, A i) = ∑ i ∈ s, Q (A i) := by
    intro s A
    induction s using Finset.induction_on with
    | empty => change d ⬝ᵥ (0 : Matrix (Fin p) (Fin p) ℝ) *ᵥ d = _; simp
    | insert k s hk ih =>
      rw [Finset.sum_insert hk, Finset.sum_insert hk, ← ih]
      change d ⬝ᵥ (Matrix.of (A k) + Matrix.of (∑ i ∈ s, A i)) *ᵥ d = _
      rw [add_mulVec, dotProduct_add]
  have hR := abs_sub_sub_le_of_hasDerivAt_two (a := 0) (b := 1)
    (c := Q ((n : ℝ) • M θ₀)) (η := (n : ℝ) * ((p : ℝ) ^ 2 * η' * ‖d‖ ^ 2))
    (g := fun t ↦ ∑ i ∈ range n, F.logLik (u t) (O i ω))
    (g' := fun t ↦ ∑ i ∈ range n, d ⬝ᵥ F.scoreVec (u t) (O i ω))
    (g'' := fun t ↦ Q (∑ i ∈ range n, ψ (O i ω) (u t)))
    (fun t ht ↦ HasDerivAt.fun_sum fun i _ ↦ by
      have := (h3 i (u t) (hball t ht)).1.comp_hasDerivAt t (hline t)
      rw [gradCLM_apply, dotProduct_comm] at this
      exact this)
    (fun t ht ↦ by
      show HasDerivAt _ (Q (∑ i ∈ range n, ψ (O i ω) (u t))) t
      rw [hQsum]
      refine HasDerivAt.fun_sum fun i _ ↦ ?_
      have := (gradCLM d).hasFDerivAt.comp_hasDerivAt t
        ((h3 i (u t) (hball t ht)).2.comp_hasDerivAt t (hline t))
      simp only [Function.comp_def, gradCLM_apply, mulVecCLM_apply] at this
      exact this)
    (fun t ht ↦ by
      have e1 := h2 (u t) (hball t ht)
      have e2 := hMδ (lt_of_lt_of_le (hmem t ht) (min_le_left _ _))
      have hsplit : ∑ i ∈ range n, ψ (O i ω) (u t) - (n : ℝ) • M θ₀ =
          (n : ℝ) • ((n : ℝ)⁻¹ • ∑ i ∈ range n, ψ (O i ω) (u t) - M θ₀) := by
        rcases Nat.eq_zero_or_pos n with rfl | hn
        · simp
        · rw [smul_sub, smul_smul, mul_inv_cancel₀ (by positivity), one_smul]
      have hle : ‖(n : ℝ)⁻¹ • ∑ i ∈ range n, ψ (O i ω) (u t) - M θ₀‖ ≤ η' := by
        rw [dist_eq_norm] at e1 e2
        calc _ ≤ ‖(n : ℝ)⁻¹ • ∑ i ∈ range n, ψ (O i ω) (u t) - M (u t)‖ +
              ‖M (u t) - M θ₀‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
          _ ≤ η' := by linarith
      rw [← hQsub, hsplit, hQsmul, abs_mul, abs_of_nonneg (Nat.cast_nonneg _)]
      refine mul_le_mul_of_nonneg_left ((abs_dotProduct_of_mulVec_le _ d).trans ?_)
        (Nat.cast_nonneg _)
      gcongr)
    (by simp only [hu, zero_smul, add_zero, ← dotProduct_sum, h4, dotProduct_zero])
  have hu0 : u 0 = a := by simp [hu]
  have hu1 : u 1 = θ₀ := by simp [hu, hd]
  simp only [sub_zero, one_pow, mul_one, hu0, hu1] at hR
  have hc : Q ((n : ℝ) • M θ₀) = -((n : ℝ) * ((a - θ₀) ⬝ᵥ I *ᵥ (a - θ₀))) := by
    rw [hQsmul]
    simp only [hQ, hMI, neg_mulVec, dotProduct_neg, hd]
    rw [show θ₀ - a = -(a - θ₀) by abel, mulVec_neg, dotProduct_neg, neg_dotProduct, neg_neg,
      mul_neg]
  rw [hc] at hR
  have key : (F.lrStatVec O θh θ₀ - waldStatVec θh θ₀ fun _ _ ↦ I) n ω =
      -2 * (∑ i ∈ range n, F.logLik θ₀ (O i ω) - ∑ i ∈ range n, F.logLik a (O i ω) -
        -((n : ℝ) * ((a - θ₀) ⬝ᵥ I *ᵥ (a - θ₀))) / 2) := by
    simp only [Pi.sub_apply, lrStatVec, waldStatVec, ← ha, Finset.sum_sub_distrib]
    ring
  have hd' : ‖d‖ ≤ ‖(WithLp.toLp 2 a - WithLp.toLp 2 θ₀ : EuclideanSpace ℝ (Fin p))‖ := by
    rw [hd, norm_sub_rev]; exact norm_sub_le_norm_toLp_sub a θ₀
  have h2p : 2 * ((p : ℝ) ^ 2 * η') ≤ η := by
    have e : 2 * ((p : ℝ) ^ 2 * η') = η * ((p : ℝ) ^ 2 / ((p : ℝ) ^ 2 + 1)) := by
      rw [hη']; field_simp
    rw [e]
    exact mul_le_of_le_one_right hη.le (div_le_one_of_le₀ (by linarith) (by positivity))
  rw [key, abs_mul, norm_smul, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _), mul_pow,
    Real.sq_sqrt (Nat.cast_nonneg _)]
  calc |(-2 : ℝ)| * |∑ i ∈ range n, F.logLik θ₀ (O i ω) - ∑ i ∈ range n, F.logLik a (O i ω) -
        -((n : ℝ) * ((a - θ₀) ⬝ᵥ I *ᵥ (a - θ₀))) / 2|
      ≤ 2 * ((n : ℝ) * ((p : ℝ) ^ 2 * η' * ‖d‖ ^ 2)) := by
        rw [abs_neg, abs_two]; gcongr
    _ = (n : ℝ) * (2 * ((p : ℝ) ^ 2 * η') * ‖d‖ ^ 2) := by ring
    _ ≤ (n : ℝ) * (η * ‖(WithLp.toLp 2 a - WithLp.toLp 2 θ₀ :
          EuclideanSpace ℝ (Fin p))‖ ^ 2) := by gcongr
    _ = _ := by ring

/-- **Wilks' theorem for a vector parameter.** Under the hypotheses of
`lrStatVec_sub_waldStatVec_tendstoInMeasure` and joint measurability of `(θ, z) ↦ ℓ(θ; z)`,
the likelihood ratio statistic `Λ_n = 2 ∑_{i < n} (ℓ(θ̂_n; O_i) - ℓ(θ₀; O_i))` converges in
distribution to every variable with law `χ²_p`. -/
theorem lrStatVec_tendstoInDistribution (hO : IsIIDSample O μ)
    (hlaw : μ.map (O 0) = F.law θ₀) (hreg : F.IsRegularAtVec θ₀) {r : ℝ}
    (hs : F.IsScoreRegularVec θ₀ r) (hI : (F.fisherInfoMatrix θ₀).PosDef)
    (hjoint : Measurable fun q : (Fin p → ℝ) × S ↦ F.logLik q.1 q.2)
    {θh : ℕ → Ω → Fin p → ℝ} (hθm : ∀ n, AEMeasurable (θh n) μ)
    (hθ : TendstoInMeasure μ θh atTop (fun _ ↦ θ₀))
    (hroot : WithProbTendingToOne μ
      (fun n ↦ {ω | ∑ i ∈ range n, F.scoreVec (θh n ω) (O i ω) = 0}))
    {Ω'' : Type*} {mΩ'' : MeasurableSpace Ω''} {P'' : Measure Ω''} [IsProbabilityMeasure P'']
    {W : Ω'' → ℝ} (hW : HasLaw W (chiSquared p) P'') :
    TendstoInDistribution (F.lrStatVec O θh θ₀) atTop W (fun _ ↦ μ) P'' := by
  have hN := mle_tendstoInDistribution_vec hO hlaw hreg hs hI hθm hθ hroot
    (P' := multivariateGaussian 0 (F.fisherInfoMatrix θ₀)⁻¹) (Y := id) HasLaw.id
  have hWald := waldStatVec_tendstoInDistribution hI HasLaw.id hN
    (Ih := fun _ _ ↦ F.fisherInfoMatrix θ₀) (fun j k ↦ tendstoInMeasure_const _)
    (fun _ _ _ ↦ aemeasurable_const) hW
  refine tendstoInDistribution_of_tendstoInMeasure_sub _ W hWald
    (lrStatVec_sub_waldStatVec_tendstoInMeasure hO hlaw hreg hs hI hθm hθ hroot) fun n ↦ ?_
  have hX := hO.aemeasurable
  exact (Finset.aemeasurable_fun_sum _ fun i _ ↦
    (hjoint.comp_aemeasurable ((hθm n).prodMk (hX i))).sub
      (hjoint.comp_aemeasurable (aemeasurable_const.prodMk (hX i)))).const_mul 2

end ParametricFamily

end CausalInference
