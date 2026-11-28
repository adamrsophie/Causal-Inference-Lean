/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.Estimation.LogisticFitNormalityScore
public import CausalInference.PopulationAdjustment.BayesStandardizationLogistic

/-!
# Asymptotic normality of the logistic maximum likelihood fit

Let `O` be an i.i.d. sample of records `(c, y)` whose law is the logistic family `P_{ξ₀}` with a
regressor law `R`, a design `z` bounded `R`-almost surely and of full rank under `R`, and let
`ξ̂_n` be the maximum likelihood fit over a compact neighborhood `K` of `ξ₀`. Then

  `√n (ξ̂_n - ξ₀) ⇒ N(0, I(ξ₀)⁻¹)`,  `I(ξ₀) = ∫ σ(z ⬝ ξ₀) (1 - σ(z ⬝ ξ₀)) z zᵀ dR`

(`tendstoInDistribution_sqrt_smul_glmMLE_logistic`). The proof applies the vector Z-estimator
theorem to the logistic score in Euclidean coordinates: the score has mean zero and is bounded,
its derivative is dominated by the constant `B²`, bread and meat are both `I(ξ₀)`, the fit is
consistent and is a root of the score equations with probability tending to one, since it lies
in the interior of `K`. The result is moved from `EuclideanSpace ℝ κ` back to `κ → ℝ` along the
continuous map `ofLp`.

The fit is the maximizer chosen by `Classical.choose`, and its measurability is not derived
here; it is the single hypothesis `hξm` beyond the model. Every other premise of the
Z-estimator theorem is proved, among them consistency (`tendstoInMeasure_glmMLE_logisticFamily`)
and the regressor marginal of the record law (`map_fst_logisticFamily_law`).

For a randomized trial with a logistic outcome model the theorem reads
`Trial.LogisticOutcomeModel.tendstoInDistribution_glmMLE`, with limit `logisticLimit`.

## Main results

* `map_fst_logisticFamily_law`, `tendstoInMeasure_glmMLE_logisticFamily`.
* `tendstoInDistribution_sqrt_smul_glmMLE_logistic`.
* `Trial.LogisticOutcomeModel.tendstoInDistribution_glmMLE`,
  `Trial.LogisticOutcomeModel.posDef_logisticInfo`.

## References

* A. W. van der Vaart, *Asymptotic Statistics*, Cambridge University Press (1998), chapter 5.
* P. McCullagh and J. A. Nelder, *Generalized Linear Models*, 2nd edition, Chapman and Hall
  (1989), chapter 4.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology Set Matrix Finset
open scoped ENNReal NNReal

namespace CausalInference

namespace PosteriorLimit

open PopulationAdjustment PopulationAdjustment.BayesStandardization

variable {C κ : Type*} [Fintype κ] [MeasurableSpace C] {R : Measure C} [IsProbabilityMeasure R]
  {z : C → κ → ℝ} {hz : ∀ j, Measurable fun c ↦ z c j}

/-- **The regressor marginal of the logistic family is the regressor law**: the first
coordinate of a record with law `P_{ξ₀}` has law `R`. -/
theorem map_fst_logisticFamily_law (ξ₀ : κ → ℝ) :
    ((glmFamily logisticKernel R z hz).law ξ₀).map Prod.fst = R := by
  ext s hs
  rw [Measure.map_apply measurable_fst hs]
  change (R.prod (Measure.dirac (0 : ℝ) + Measure.dirac 1)).withDensity
    (fun q ↦ ENNReal.ofReal (logisticDens (z q.1 ⬝ᵥ ξ₀) q.2)) (Prod.fst ⁻¹' s) = R s
  have hm : Measurable fun q : C × ℝ ↦ ENNReal.ofReal (logisticDens (z q.1 ⬝ᵥ ξ₀) q.2) :=
    ENNReal.measurable_ofReal.comp
      ((glmFamily logisticKernel R z hz).measurable_density ξ₀)
  rw [withDensity_apply _ (measurable_fst hs), show Prod.fst ⁻¹' s = s ×ˢ (univ : Set ℝ) by
    ext; simp, ← Measure.prod_restrict, Measure.restrict_univ, lintegral_prod _ hm.aemeasurable]
  have hin : ∀ c, ∫⁻ y, ENNReal.ofReal (logisticDens (z c ⬝ᵥ ξ₀) y)
      ∂(Measure.dirac (0 : ℝ) + Measure.dirac 1) = 1 := fun c ↦ by
    rw [lintegral_add_measure, lintegral_dirac, lintegral_dirac, logisticDens_zero,
      logisticDens_one, ← ENNReal.ofReal_add (sub_nonneg.2 (Real.sigmoid_lt_one _).le)
        (Real.sigmoid_pos _).le]
    simp
  simp only [hin, lintegral_const, Measure.restrict_apply MeasurableSet.univ, univ_inter,
    one_mul]

variable {Ξ : Type*} [MeasurableSpace Ξ] {P : Measure Ξ} [IsProbabilityMeasure P]
  {O : ℕ → Ξ → C × ℝ} {K : Set (κ → ℝ)} {ξ₀ : κ → ℝ} {B : ℝ}

/-- Full rank under the regressor law gives full rank under the record law. -/
lemma fullRank_logisticFamily_law (hfull : ∀ v : κ → ℝ, (∀ᵐ c ∂R, z c ⬝ᵥ v = 0) → v = 0)
    (v : κ → ℝ) (h : ∀ᵐ q ∂(glmFamily logisticKernel R z hz).law ξ₀, z q.1 ⬝ᵥ v = 0) :
    v = 0 := by
  refine hfull v ?_
  have h2 := (ae_map_iff measurable_fst.aemeasurable
    (measurableSet_eq_fun (measurable_dotProduct_design hz v) measurable_const)).2 h
  rwa [map_fst_logisticFamily_law (R := R) (hz := hz) ξ₀] at h2

/-- **Consistency of the logistic fit from the record law alone.** For an i.i.d. sample with law
`P_{ξ₀}`, a design bounded and of full rank under `R`, and a compact `K ∋ ξ₀`, the maximum
likelihood fit over `K` converges in probability to `ξ₀`. -/
theorem tendstoInMeasure_glmMLE_logisticFamily (hO : IsIIDSample O P)
    (hlaw : P.map (O 0) = (glmFamily logisticKernel R z hz).law ξ₀)
    (hB : ∀ᵐ c ∂R, ∀ j, |z c j| ≤ B) (hfull : ∀ v : κ → ℝ, (∀ᵐ c ∂R, z c ⬝ᵥ v = 0) → v = 0)
    (hK : IsCompact K) (hξ₀ : ξ₀ ∈ K) :
    TendstoInMeasure P (glmMLE logisticDens z K O) atTop (fun _ ↦ ξ₀) := by
  have := ParametricFamily.isProbabilityMeasure_law (F := glmFamily logisticKernel R z hz)
    (Set.mem_univ ξ₀)
  have hid : ((glmFamily logisticKernel R z hz).law ξ₀).map (fun q : C × ℝ ↦ (q.1, q.2)) =
      (glmFamily logisticKernel R z hz).law ξ₀ := Measure.map_id
  exact tendstoInMeasure_logisticMLE (μ := (glmFamily logisticKernel R z hz).law ξ₀)
    measurable_fst measurable_snd (map_fst_logisticFamily_law ξ₀) hid
    (fullRank_logisticFamily_law hfull)
    (fun j ↦ integrable_of_ae_abs_le ((hz j).comp measurable_fst)
      ((ae_abs_design_le hB).mono fun _ hq ↦ hq j)) hK hξ₀ hO (hlaw.trans hid.symm)

omit [IsProbabilityMeasure P] in
/-- Bounded measurable functions are square integrable, coordinatewise for the logistic
score. -/
lemma memLp_logisticEstFun (hO : IsIIDSample O P)
    (hlaw : P.map (O 0) = (glmFamily logisticKernel R z hz).law ξ₀)
    (hB : ∀ᵐ c ∂R, ∀ j, |z c j| ≤ B) :
    MemLp (fun ω ↦ logisticEstFun z (O 0 ω) (WithLp.toLp 2 ξ₀)) 2 P := by
  have := ParametricFamily.isProbabilityMeasure_law (F := glmFamily logisticKernel R z hz)
    (Set.mem_univ ξ₀)
  refine memLp_piLp_iff.2 fun k ↦ ?_
  have hm : Measurable fun q : C × ℝ ↦ logisticEstFun z q (WithLp.toLp 2 ξ₀) k :=
    (measurable_logisticDensScore_design hz ξ₀).mul ((hz k).comp measurable_fst)
  refine (memLp_map_measure_iff (g := fun q : C × ℝ ↦ logisticEstFun z q (WithLp.toLp 2 ξ₀) k)
    hm.aestronglyMeasurable (hO.aemeasurable 0)).1 ?_
  rw [hlaw]
  refine MemLp.of_bound hm.aestronglyMeasurable (max B 0)
    ((ae_abs_design_le hB).mono fun q hq ↦ ?_)
  rw [Real.norm_eq_abs, logisticEstFun_apply, WithLp.ofLp_toLp, abs_mul]
  calc |logisticDensScore (z q.1 ⬝ᵥ ξ₀) q.2| * |z q.1 k| ≤ 1 * max B 0 :=
        mul_le_mul (abs_logisticDensScore_le _ _) (hq k) (abs_nonneg _) zero_le_one
    _ = max B 0 := one_mul _

omit [MeasurableSpace C] [IsProbabilityMeasure P] in
/-- The logistic fit in Euclidean coordinates is a root of the score equations with
probability tending to one. -/
lemma withProbTendingToOne_sum_logisticEstFun_glmMLE (hK : IsCompact K) (hKξ₀ : K ∈ 𝓝 ξ₀)
    (hcons : TendstoInMeasure P (glmMLE logisticDens z K O) atTop (fun _ ↦ ξ₀)) :
    WithProbTendingToOne P fun n ↦ {ω | ∑ i ∈ range n,
      logisticEstFun z (O i ω) (WithLp.toLp 2 (glmMLE logisticDens z K O n ω)) = 0} := by
  refine (withProbTendingToOne_logisticScoreSum_glmMLE_eq_zero hK hKξ₀ hcons).mono
    fun n ω h ↦ ?_
  simp only [Set.mem_ofPred_eq] at h ⊢
  have e : ∑ i ∈ range n,
      logisticEstFun z (O i ω) (WithLp.toLp 2 (glmMLE logisticDens z K O n ω)) =
      WithLp.toLp 2 (logisticScoreSum z (fun i : Fin n ↦ O i ω)
        (glmMLE logisticDens z K O n ω)) := by
    rw [logisticScoreSum, WithLp.toLp_sum, ← Fin.sum_univ_eq_sum_range
      (fun i ↦ logisticEstFun z (O i ω) (WithLp.toLp 2 (glmMLE logisticDens z K O n ω)))]
    rfl
  rw [e, h]
  rfl

variable [DecidableEq κ]

/-- The law `N(0, I⁻¹)` on `κ → ℝ` pulled back to Euclidean coordinates. -/
lemma hasLaw_toLp_of_hasLaw {Ω' : Type*} {mΩ' : MeasurableSpace Ω'} {P' : Measure Ω'}
    {S : Matrix κ κ ℝ} {Y : Ω' → κ → ℝ}
    (hY : HasLaw Y ((multivariateGaussian 0 S).map (PiLp.continuousLinearEquiv 2 ℝ
      fun _ : κ ↦ ℝ)) P') :
    HasLaw (fun ω ↦ WithLp.toLp 2 (Y ω)) (multivariateGaussian 0 S) P' := by
  have h : HasLaw (WithLp.toLp 2 : (κ → ℝ) → EuclideanSpace ℝ κ) (multivariateGaussian 0 S)
      ((multivariateGaussian 0 S).map (PiLp.continuousLinearEquiv 2 ℝ fun _ : κ ↦ ℝ)) :=
    ⟨(PiLp.continuous_toLp 2 _).measurable.aemeasurable, by
      rw [Measure.map_map (PiLp.continuous_toLp 2 _).measurable (by fun_prop)]
      exact Measure.map_id⟩
  exact h.comp hY


/-- **Asymptotic normality of the logistic maximum likelihood fit.** Let `O` be an i.i.d.
sample with law `P_{ξ₀}` of the logistic family with regressor law `R`, the design bounded by
`B` and of full rank `R`-almost surely, `K` a compact neighborhood of `ξ₀`, and the fit
`ξ̂_n` over `K` almost everywhere measurable. Then `√n (ξ̂_n - ξ₀)` converges in distribution
to every random vector with law `N(0, I(ξ₀)⁻¹)` on `κ → ℝ`. -/
theorem tendstoInDistribution_sqrt_smul_glmMLE_logistic (hO : IsIIDSample O P)
    (hlaw : P.map (O 0) = (glmFamily logisticKernel R z hz).law ξ₀)
    (hB : ∀ᵐ c ∂R, ∀ j, |z c j| ≤ B) (hfull : ∀ v : κ → ℝ, (∀ᵐ c ∂R, z c ⬝ᵥ v = 0) → v = 0)
    (hK : IsCompact K) (hKξ₀ : K ∈ 𝓝 ξ₀)
    (hξm : ∀ n, AEMeasurable (glmMLE logisticDens z K O n) P)
    {Ω' : Type*} {mΩ' : MeasurableSpace Ω'} {P' : Measure Ω'} [IsProbabilityMeasure P']
    {Y : Ω' → κ → ℝ}
    (hY : HasLaw Y ((multivariateGaussian 0 (logisticInfo R z ξ₀)⁻¹).map
      (PiLp.continuousLinearEquiv 2 ℝ fun _ : κ ↦ ℝ)) P') :
    TendstoInDistribution (fun (n : ℕ) ω ↦ √(n : ℝ) • (glmMLE logisticDens z K O n ω - ξ₀))
      atTop Y (fun _ ↦ P) P' := by
  have hzm : Measurable z := measurable_pi_iff.2 hz
  have hI := posDef_logisticInfo hzm hB hfull ξ₀
  have hcons := tendstoInMeasure_glmMLE_logisticFamily hO hlaw hB hfull hK
    (mem_of_mem_nhds hKξ₀)
  have hψm : Measurable fun q : C × ℝ ↦ logisticEstFun z q (WithLp.toLp 2 ξ₀) :=
    (WithLp.measurable_toLp 2 _).comp (measurable_pi_iff.2 fun k ↦
      (measurable_logisticDensScore_design hz ξ₀).mul ((hz k).comp measurable_fst))
  have hJm : ∀ θ ∈ Metric.closedBall (WithLp.toLp 2 ξ₀ : EuclideanSpace ℝ κ) 1, ∀ i j,
      Measurable fun q : C × ℝ ↦ logisticEstJac z q θ i j := fun θ _ i j ↦
    ((((measurable_sigmoidWeight_dotProduct hzm (WithLp.ofLp θ)).mul (hz i)).mul
      (hz j)).comp measurable_fst).neg
  have hcont : ∀ q : C × ℝ, ∀ i j, Continuous fun θ : EuclideanSpace ℝ κ ↦
      logisticEstJac z q θ i j := fun q i j ↦
    (((continuous_sigmoidWeight.comp
      (continuous_const.dotProduct (PiLp.continuous_ofLp 2 _))).mul continuous_const).mul
      continuous_const).neg
  have hdom : ∀ᵐ q ∂(P.map (O 0)), ∀ θ ∈ Metric.closedBall
      (WithLp.toLp 2 ξ₀ : EuclideanSpace ℝ κ) 1, ∀ i j,
      |logisticEstJac z q θ i j| ≤ (fun _ ↦ (max B 0) ^ 2) q := by
    rw [hlaw]
    refine (ae_abs_design_le hB).mono fun q hq θ _ i j ↦ ?_
    simp only [logisticEstJac, Matrix.of_apply, abs_neg]
    have h1 : |sigmoidWeight (z q.1 ⬝ᵥ WithLp.ofLp θ)| ≤ 1 := by
      rw [abs_of_pos (sigmoidWeight_pos _)]; exact sigmoidWeight_le_one _
    simpa using abs_mul_le_of_abs_le (le_max_right B 0) h1 abs_one.le (hq i) (hq j)
  have hzero : P[fun ω ↦ logisticEstFun z (O 0 ω) (WithLp.toLp 2 ξ₀)] = 0 := by
    rw [← integral_map (hO.aemeasurable 0) hψm.aestronglyMeasurable, hlaw,
      integral_logisticEstFun_eq_zero hB]
  have hA : (breadMatrix (P.map (O 0)) (logisticEstJac z) (WithLp.toLp 2 ξ₀)).det ≠ 0 := by
    rw [hlaw, breadMatrix_logisticEstJac hB]; exact hI.det_pos.ne'
  have hYE := hasLaw_toLp_of_hasLaw hY
  rw [← sandwich_logisticInfo (hz := hz) hB hI, ← hlaw] at hYE
  have h := vectorZEstimator_tendstoInDistribution_of_root hO one_pos hψm hJm
    (ae_of_all _ fun q θ _ ↦ hasFDerivAt_logisticEstFun z q θ)
    (ae_of_all _ fun q i j ↦ (hcont q i j).continuousOn) (integrable_const _) hdom hzero
    (memLp_logisticEstFun hO hlaw hB) hA
    (θh := fun n ω ↦ WithLp.toLp 2 (glmMLE logisticDens z K O n ω))
    (fun n ↦ (PiLp.continuous_toLp 2 _).measurable.comp_aemeasurable (hξm n))
    (hcons.comp_continuousAt (PiLp.continuous_toLp 2 _).continuousAt)
    (withProbTendingToOne_sum_logisticEstFun_glmMLE hK hKξ₀ hcons) hYE
  exact h.continuous_comp (PiLp.continuous_ofLp 2 _)

end PosteriorLimit

/-! ### The trial form -/

namespace IndirectComparison

open PosteriorLimit PopulationAdjustment

variable {Ω₁ Ξ 𝒳 κ : Type*} [MeasurableSpace Ω₁] [MeasurableSpace Ξ] [MeasurableSpace 𝒳]
  [Fintype κ] [DecidableEq κ] {T : Trial Ω₁ 𝒳 Bool} [IsProbabilityMeasure T.μ]
  {z : 𝒳 × Bool → κ → ℝ} {ξ₀ : κ → ℝ}

omit [DecidableEq κ] in
/-- **The information of a randomized trial with a logistic outcome model is positive
definite** when the design is bounded almost surely: full rank of the design and positivity of
the weight `σ (1 - σ)` give `vᵀ I(ξ₀) v > 0` for `v ≠ 0`. -/
theorem Trial.LogisticOutcomeModel.posDef_logisticInfo (hT : T.IsRandomizedTwoArm)
    (hM : T.LogisticOutcomeModel z ξ₀) {B : ℝ}
    (hB : ∀ᵐ ω ∂T.μ, ∀ j, |z (T.X ω, T.A ω) j| ≤ B) :
    (logisticInfo (T.μ.map fun ω ↦ (T.X ω, T.A ω)) z ξ₀).PosDef := by
  have hXA : Measurable fun ω ↦ (T.X ω, T.A ω) := hT.measurable_X.prodMk hT.measurable_A
  have hset : MeasurableSet {c : 𝒳 × Bool | ∀ j, |z c j| ≤ B} := by
    simp only [Set.ofPred_forall]
    exact MeasurableSet.iInter fun j ↦
      measurableSet_le (continuous_abs.measurable.comp (hM.measurable_z j)) measurable_const
  exact PosteriorLimit.posDef_logisticInfo (measurable_pi_iff.2 hM.measurable_z)
    ((ae_map_iff hXA.aemeasurable hset).2 hB)
    (fun v hv ↦ hM.full_rank v (ae_of_ae_map hXA.aemeasurable hv)) ξ₀

/-- **Asymptotic normality of the logistic fit in a randomized trial.** Let the records
`((X, A), Y)` of a randomized trial follow the logistic outcome model at `ξ₀` with a design
bounded by `B` almost surely, `O` an i.i.d. sample of the records, `K` a compact neighborhood of
`ξ₀` and the fit `ξ̂_n` over `K` almost everywhere measurable. Then `√n (ξ̂_n - ξ₀)` converges in
distribution to every random vector with law `N(0, I(ξ₀)⁻¹)`, the information of
`law(X, A)`. -/
theorem Trial.LogisticOutcomeModel.tendstoInDistribution_glmMLE
    (hT : T.IsRandomizedTwoArm) (hM : T.LogisticOutcomeModel z ξ₀) {B : ℝ}
    (hB : ∀ᵐ ω ∂T.μ, ∀ j, |z (T.X ω, T.A ω) j| ≤ B) {K : Set (κ → ℝ)} (hK : IsCompact K)
    (hKξ₀ : K ∈ 𝓝 ξ₀) {P : Measure Ξ} [IsProbabilityMeasure P]
    {O : ℕ → Ξ → (𝒳 × Bool) × ℝ} (hO : IsIIDSample O P)
    (hlaw : P.map (O 0) = T.μ.map fun ω ↦ ((T.X ω, T.A ω), T.obsOutcome ω))
    (hξm : ∀ n, AEMeasurable (glmMLE logisticDens z K O n) P)
    {Ω' : Type*} {mΩ' : MeasurableSpace Ω'} {P' : Measure Ω'} [IsProbabilityMeasure P']
    {Y : Ω' → κ → ℝ} (hY : HasLaw Y (logisticLimit (T.μ.map fun ω ↦ (T.X ω, T.A ω)) z ξ₀) P') :
    TendstoInDistribution (fun (n : ℕ) ω ↦ √(n : ℝ) • (glmMLE logisticDens z K O n ω - ξ₀))
      atTop Y (fun _ ↦ P) P' := by
  have hXA : Measurable fun ω ↦ (T.X ω, T.A ω) := hT.measurable_X.prodMk hT.measurable_A
  have hset : MeasurableSet {c : 𝒳 × Bool | ∀ j, |z c j| ≤ B} := by
    simp only [Set.ofPred_forall]
    exact MeasurableSet.iInter fun j ↦
      measurableSet_le (continuous_abs.measurable.comp (hM.measurable_z j)) measurable_const
  exact tendstoInDistribution_sqrt_smul_glmMLE_logistic hO (hlaw.trans hM.law_eq)
    ((ae_map_iff hXA.aemeasurable hset).2 hB)
    (fun v hv ↦ hM.full_rank v (ae_of_ae_map hXA.aemeasurable hv)) hK hKξ₀ hξm hY

end IndirectComparison

end CausalInference
