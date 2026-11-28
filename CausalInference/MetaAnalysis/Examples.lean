/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.MetaAnalysis.CochranQLaw
public import CausalInference.MetaAnalysis.ISquared
public import CausalInference.MetaAnalysis.GaussianLikelihood
public import CausalInference.IndirectComparison.CommonComparator

/-!
# Meta-analysis: a worked example and the bridge to the indirect comparison

**Three studies.** Estimates `y = (0, 1, 2)` with variances `v = (1, 1/2, 1/4)`, so the weights
are `w = (1, 2, 4)` with total `7`. The pooled estimate is `10/7` with variance `1/7`,
Cochran's `Q` is `26/7` on `2` degrees of freedom, `H² = 13/7`, `I² = 6/13`, and the slope of
`E[Q]` in `τ²` is `c = 4` (`example_ivwEstimate`, `example_cochranQ`, `example_hSquared`,
`example_iSquared`, `example_cochranQSlope`). Under `⊗ᵢ N(θ, vᵢ)` every theorem of the common
effect model applies with all hypotheses discharged (`example_gaussianModel`): `θ̂` is unbiased
with variance `1/7`, `E[Q] = 2`, `Q ~ χ²₂` independently of `θ̂ ~ N(θ, 1/7)`, and `θ̂` is
efficient. With a between study variance `τ²`, `E[Q] = 2 + 4 τ²`, both for `Yᵢ ~ N(θ, vᵢ + τ²)`
and for the components form `Yᵢ = θ + bᵢ + εᵢ` (`example_integral_cochranQ_of_variance_add`,
`example_integral_cochranQ_of_components`).

**The indirect comparison.** Two independent sets of studies estimate the effects `d_ac` and
`d_bc` of a common comparator; their pooled estimates feed the indirect estimate
`d̂_ac - d̂_bc` (`IndirectComparison.indirectEstimate`), which is unbiased for `d_ac - d_bc` with
variance `1 / ∑ wᵢ + 1 / ∑ uⱼ` (`indirectEstimate_ivwEstimate`). A concrete instance on a product
of Gaussian laws: `indirectEstimate_ivwEstimate_example`.

## Main results

* `example_ivwEstimate`, `example_cochranQ`, `example_hSquared`, `example_iSquared`,
  `example_cochranQSlope`, `example_gaussianModel`.
* `example_integral_cochranQ_of_variance_add`, `example_integral_cochranQ_of_components`,
  `example_quadForm_one`, `example_equalWeights`, `example_iSquared_integral_cochranQ`,
  `example_hasLaw_ivwEstimate_cochranQ`, `example_variance_ivwEstimate_le`,
  `example_stdGaussian_map_sum_sq_tStat`.
* `indirectEstimate_ivwEstimate`, `indirectEstimate_ivwEstimate_example`.
-/

@[expose] public section

namespace CausalInference

namespace MetaAnalysis

open MeasureTheory ProbabilityTheory Finset IndirectComparison

/-! ### Three studies -/

/-- The variances `(1, 1/2, 1/4)` of the example. -/
noncomputable def exampleVar : Fin 3 → ℝ := ![1, 1 / 2, 1 / 4]

/-- The estimates `(0, 1, 2)` of the example. -/
noncomputable def exampleY : Fin 3 → ℝ := ![0, 1, 2]

theorem exampleVar_pos : ∀ i, 0 < exampleVar i := by
  intro i; fin_cases i <;> norm_num [exampleVar]

theorem example_sum_ivWeight : ∑ i, ivWeight exampleVar i = 7 := by
  norm_num [ivWeight, exampleVar, Fin.sum_univ_three]

/-- The pooled estimate of the example is `10/7`. -/
theorem example_ivwEstimate : ivwEstimate exampleVar exampleY = 10 / 7 := by
  norm_num [ivwEstimate, PopulationAdjustment.weightedMean, ivWeight, exampleVar, exampleY,
    Fin.sum_univ_three]

/-- Cochran's `Q` of the example is `26/7`. -/
theorem example_cochranQ : cochranQ exampleVar exampleY = 26 / 7 := by
  rw [cochranQ, example_ivwEstimate]
  norm_num [ivWeight, exampleVar, exampleY, Fin.sum_univ_three]

/-- `H² = 13/7` in the example. -/
theorem example_hSquared : hSquared (cochranQ exampleVar exampleY) 3 = 13 / 7 := by
  rw [example_cochranQ, hSquared]
  norm_num

/-- `I² = 6/13` in the example. -/
theorem example_iSquared : iSquared (cochranQ exampleVar exampleY) 3 = 6 / 13 := by
  rw [example_cochranQ, iSquared_of_pos (by norm_num)]
  norm_num

/-- The slope `c = ∑ wᵢ - ∑ wᵢ² / ∑ wᵢ` of the example is `7 - 21/7 = 4`. -/
theorem example_cochranQSlope : cochranQSlope exampleVar = 4 := by
  rw [cochranQSlope, example_sum_ivWeight]
  norm_num [ivWeight, exampleVar, Fin.sum_univ_three]

/-- **The common effect theorems on the example, with all hypotheses verified.** Under
`⊗ᵢ N(θ, vᵢ)` with the variances of the example: `θ̂` is unbiased with variance `1/7`,
`E[Q] = 2`, `Q ~ χ²₂`, `θ̂ ~ N(θ, 1/7)`, `θ̂` and `Q` are independent, and `θ̂` is an efficient
estimator in the Gaussian family. -/
theorem example_gaussianModel (θ : ℝ) :
    ∫ y, ivwEstimate exampleVar y
        ∂(Measure.pi fun i => gaussianReal θ (exampleVar i).toNNReal) = θ ∧
      Var[ivwEstimate exampleVar; Measure.pi fun i => gaussianReal θ (exampleVar i).toNNReal] =
        1 / 7 ∧
      ∫ y, cochranQ exampleVar y
        ∂(Measure.pi fun i => gaussianReal θ (exampleVar i).toNNReal) = 2 ∧
      HasLaw (cochranQ exampleVar) (chiSquared 2)
        (Measure.pi fun i => gaussianReal θ (exampleVar i).toNNReal) ∧
      HasLaw (ivwEstimate exampleVar) (gaussianReal θ (1 / 7 : ℝ).toNNReal)
        (Measure.pi fun i => gaussianReal θ (exampleVar i).toNNReal) ∧
      IndepFun (ivwEstimate exampleVar) (cochranQ exampleVar)
        (Measure.pi fun i => gaussianReal θ (exampleVar i).toNNReal) ∧
      (commonEffectFamily exampleVar_pos).IsEfficient (ivwEstimate exampleVar) id := by
  have hG := isGaussianCommonEffectModel_pi exampleVar_pos θ
  have h := hG.isCommonEffectModel
  obtain ⟨h1, h2⟩ := h.integral_variance_ivwEstimate
  obtain ⟨-, h3⟩ := h.integral_cochranQ
  obtain ⟨h4, h5, h6⟩ := hG.hasLaw_cochranQ (m := 2) (by simp)
  rw [example_sum_ivWeight] at h2 h5
  refine ⟨h1, h2, ?_, h4, h5, h6, isEfficient_ivwEstimate exampleVar_pos⟩
  rw [h3]
  norm_num

/-- **`E[Q]` under a between study variance, on the example.** If the estimates are independent
with `Yᵢ ~ N(θ, vᵢ + τ²)`, `τ² ≥ 0`, and `Q` uses the within-study variances `vᵢ` of the
example, then `E[Q] = 2 + 4 τ²`. -/
theorem example_integral_cochranQ_of_variance_add (θ : ℝ) {τ2 : ℝ} (hτ : 0 ≤ τ2) :
    ∫ y, cochranQ exampleVar (fun i => y i)
        ∂(Measure.pi fun i => gaussianReal θ (exampleVar i + τ2).toNNReal) = 2 + 4 * τ2 := by
  have h := (isGaussianCommonEffectModel_pi (v := fun i => exampleVar i + τ2)
    (fun i => add_pos_of_pos_of_nonneg (exampleVar_pos i) hτ) θ).isCommonEffectModel
  have := h.isProbabilityMeasure
  rw [integral_cochranQ_of_variance_add exampleVar_pos h.memLp h.integral_eq h.variance_eq
    (fun i j hij => h.covariance_eq_zero hij), example_cochranQSlope]
  norm_num
  ring

/-- **`E[Q]` in the components form, on the example.** Study effects `bᵢ ~ N(0, τ²)`, `τ² > 0`,
and errors `εᵢ ~ N(0, vᵢ)` with the variances of the example, all independent (the product of
`⊗ᵢ N(0, τ²)` and `⊗ᵢ N(0, vᵢ)`): for `Yᵢ = θ + bᵢ + εᵢ`, `E[Q] = 2 + 4 τ²`. -/
theorem example_integral_cochranQ_of_components (θ : ℝ) {τ2 : ℝ} (hτ : 0 < τ2) :
    ∫ ω, cochranQ exampleVar (fun i => θ + ω.1 i + ω.2 i)
        ∂((Measure.pi fun _ : Fin 3 => gaussianReal 0 τ2.toNNReal).prod
          (Measure.pi fun i => gaussianReal 0 (exampleVar i).toNNReal)) = 2 + 4 * τ2 := by
  set μ := Measure.pi fun _ : Fin 3 => gaussianReal 0 τ2.toNNReal
  set ν := Measure.pi fun i => gaussianReal 0 (exampleVar i).toNNReal
  have hb : IsCommonEffectModel (μ.prod ν) (fun i ω => ω.1 i) 0 fun _ => τ2 :=
    (isGaussianCommonEffectModel_of_hasLaw (fun _ => hτ)
      (measurePreserving_fst (μ := μ) (ν := ν)).hasLaw).isCommonEffectModel
  have hε : IsCommonEffectModel (μ.prod ν) (fun i ω => ω.2 i) 0 exampleVar :=
    (isGaussianCommonEffectModel_of_hasLaw exampleVar_pos
      (measurePreserving_snd (μ := μ) (ν := ν)).hasLaw).isCommonEffectModel
  have := hb.isProbabilityMeasure
  have hind : IndepFun (fun ω : (Fin 3 → ℝ) × (Fin 3 → ℝ) => ω.1) (fun ω => ω.2) (μ.prod ν) :=
    indepFun_prod (X := id) (Y := id) measurable_id measurable_id
  have hbε : ∀ i j, cov[fun ω : (Fin 3 → ℝ) × (Fin 3 → ℝ) => ω.1 i, fun ω => ω.2 j;
      μ.prod ν] = 0 := fun i j =>
    (hind.comp (measurable_pi_apply i) (measurable_pi_apply j)).covariance_eq_zero
      (hb.memLp i) (hε.memLp j)
  rw [(integral_cochranQ_of_components exampleVar_pos hb.memLp hε.memLp hb.integral_eq
    hε.integral_eq hb.variance_eq hε.variance_eq (fun i j hij => hb.covariance_eq_zero hij)
    (fun i j hij => hε.covariance_eq_zero hij) hbε).2, example_cochranQSlope]
  norm_num
  ring

/-- The projector theorem with all hypotheses verified, for the identity projector of rank `3`:
`Zᵀ Z ~ χ²₃` for `Z ~ N(0, I₃)`. -/
theorem example_quadForm_one :
    (multivariateGaussian (0 : EuclideanSpace ℝ (Fin 3)) 1).map
      (quadForm (1 : Matrix (Fin 3) (Fin 3) ℝ)) = chiSquared 3 :=
  multivariateGaussian_map_quadForm_of_idempotent Matrix.transpose_one (mul_one 1)
    (by simp [Matrix.rank_one])

/-- **Equal weights on the example, with all hypotheses verified.** Under `⊗ᵢ N(θ, vᵢ)` with the
variances of the example, the equal weight average `∑ Yᵢ / 3` is unbiased for every `θ`, its
variance is `7/36`, at least the bound `1/7`, and it does not attain the bound, since its
weights are not the inverse variance weights. -/
theorem example_equalWeights (θ : ℝ) :
    (∀ θ', ∫ y, ∑ i, (1 / 3 : ℝ) * y i
        ∂(Measure.pi fun i => gaussianReal θ' (exampleVar i).toNNReal) = θ') ∧
      Var[fun y => ∑ i, (1 / 3 : ℝ) * y i;
        Measure.pi fun i => gaussianReal θ (exampleVar i).toNNReal] = 7 / 36 ∧
      1 / 7 ≤ Var[fun y => ∑ i, (1 / 3 : ℝ) * y i;
        Measure.pi fun i => gaussianReal θ (exampleVar i).toNNReal] ∧
      Var[fun y => ∑ i, (1 / 3 : ℝ) * y i;
        Measure.pi fun i => gaussianReal θ (exampleVar i).toNNReal] ≠ 1 / 7 := by
  have hM : ∀ θ', IsCommonEffectModel
      (Measure.pi fun i => gaussianReal θ' (exampleVar i).toNNReal) (fun i x => x i) θ'
      exampleVar := fun θ' =>
    (isGaussianCommonEffectModel_pi exampleVar_pos θ').isCommonEffectModel
  have h := hM θ
  have := h.isProbabilityMeasure
  have hc : ∑ _i : Fin 3, (1 / 3 : ℝ) = 1 := by norm_num
  have hunc := fun i j (hij : i ≠ j) => h.covariance_eq_zero hij
  refine ⟨?_, ?_, ?_, ?_⟩
  · refine (integral_sum_mul_eq_iff (Y := fun i (x : Fin 3 → ℝ) => x i)
      (P := fun θ' => Measure.pi fun i => gaussianReal θ' (exampleVar i).toNNReal)
      (fun θ' i => (((hM θ').memLp i).integrable one_le_two))
      (fun θ' => (hM θ').integral_eq) (fun _ => 1 / 3)).2 hc
  · rw [variance_sum_mul_of_uncorrelated h.memLp hunc]
    simp only [h.variance_eq]
    norm_num [exampleVar, Fin.sum_univ_three]
  · have := variance_sum_mul_ge exampleVar_pos h.memLp h.variance_eq hunc hc
    rwa [example_sum_ivWeight] at this
  · intro heq
    have h' := (variance_sum_mul_eq_iff exampleVar_pos h.memLp h.variance_eq hunc hc).1
      (by rw [example_sum_ivWeight]; exact heq)
    have h0 := congrFun h' 0
    rw [example_sum_ivWeight] at h0
    norm_num [ivWeight, exampleVar] at h0

/-- **`I²` as a share of between study variance, on the example**: for `Yᵢ ~ N(θ, vᵢ + τ²)`
independent, `τ² ≥ 0`, the typical within-study variance is `2/4 = 1/2` and `I²` at `E[Q]` is
`τ² / (τ² + 1/2)`. -/
theorem example_iSquared_integral_cochranQ (θ : ℝ) {τ2 : ℝ} (hτ : 0 ≤ τ2) :
    iSquared (∫ y, cochranQ exampleVar (fun i => y i)
        ∂(Measure.pi fun i => gaussianReal θ (exampleVar i + τ2).toNNReal)) 3 =
      τ2 / (τ2 + 1 / 2) := by
  have h := (isGaussianCommonEffectModel_pi (v := fun i => exampleVar i + τ2)
    (fun i => add_pos_of_pos_of_nonneg (exampleVar_pos i) hτ) θ).isCommonEffectModel
  have := h.isProbabilityMeasure
  have e := iSquared_integral_cochranQ exampleVar_pos (by simp) h.memLp h.integral_eq hτ
    h.variance_eq (fun i j hij => h.covariance_eq_zero hij)
  rw [Fintype.card_fin] at e
  rw [e, heterogeneityShare, typicalVariance, example_cochranQSlope, Fintype.card_fin]
  norm_num

/-- **The joint law with an unknown scale, on the example.** For independent
`Yᵢ ~ N(θ, 2 vᵢ)` with the variances of the example (`σ² = 2`), `(θ̂, Q / 2)` has law
`N(θ, 2/7) ⊗ χ²₂`. -/
theorem example_hasLaw_ivwEstimate_cochranQ (θ : ℝ) :
    HasLaw (fun y => (ivwEstimate exampleVar (fun i => y i),
        cochranQ exampleVar (fun i => y i) / 2))
      ((gaussianReal θ (2 / 7 : ℝ).toNNReal).prod (chiSquared 2))
      (Measure.pi fun i => gaussianReal θ (2 * exampleVar i).toNNReal) := by
  have h := hasLaw_ivwEstimate_cochranQ (m := 2) (Y := fun i (y : Fin 3 → ℝ) => y i)
    (by simp) exampleVar_pos two_pos (iIndepFun_pi (X := fun _ => id) fun _ => aemeasurable_id)
    fun i =>
      (measurePreserving_eval (fun i => gaussianReal θ (2 * exampleVar i).toNNReal) i).hasLaw
  rwa [example_sum_ivWeight] at h

/-- The Cramér-Rao theorem with all hypotheses verified, for the pooled estimate itself on the
example (the estimator compared with `θ̂` is `θ̂`, so the inequality is an equality here; the
point is that every hypothesis is met by a concrete estimator). -/
theorem example_variance_ivwEstimate_le (θ : ℝ) :
    Var[ivwEstimate exampleVar; (commonEffectFamily exampleVar_pos).law θ] ≤
      Var[ivwEstimate exampleVar; (commonEffectFamily exampleVar_pos).law θ] :=
  variance_ivwEstimate_le exampleVar_pos (isUnbiased_ivwEstimate exampleVar_pos)
    (meanDerivInterchange_ivwEstimate exampleVar_pos θ)
    (commonEffectFamily_moments exampleVar_pos θ).1

/-- The `χ²` and `t` laws of orthonormal coordinates with all hypotheses verified, for the
standard basis of `ℝ³`: `Z₁² + Z₂² + Z₃² ~ χ²₃` and `Z₀ / √((Z₁² + Z₂²) / 2) ~ t₂`. -/
theorem example_stdGaussian_map_sum_sq_tStat :
    (stdGaussian (EuclideanSpace ℝ (Fin 3))).map
        (fun z => ∑ j, inner ℝ (EuclideanSpace.basisFun (Fin 3) ℝ j) z ^ 2) = chiSquared 3 ∧
      (stdGaussian (EuclideanSpace ℝ (Fin 3))).map
        (fun z => inner ℝ (EuclideanSpace.basisFun (Fin 3) ℝ 0) z /
          √((∑ j : Fin 2, inner ℝ (EuclideanSpace.basisFun (Fin 3) ℝ j.succ) z ^ 2) / (2 : ℕ))) =
        studentT 2 := by
  set f := EuclideanSpace.basisFun (Fin 3) ℝ
  refine ⟨stdGaussian_map_sum_sq f.orthonormal, stdGaussian_map_tStat ?_⟩
  convert f.orthonormal
  exact Fin.cons_self_tail _

/-! ### Pooled direct estimates in the indirect comparison -/

section Indirect

variable {ι κ Ω : Type*} [Fintype ι] [Fintype κ] [Nonempty ι] [Nonempty κ]
  {mΩ : MeasurableSpace Ω} {P : Measure Ω} {Y : ι → Ω → ℝ} {Z : κ → Ω → ℝ} {θ₁ θ₂ : ℝ}
  {v : ι → ℝ} {u : κ → ℝ}

/-- **The indirect comparison of two pooled estimates.** If the studies `Y` of the first
comparison and `Z` of the second each follow the common effect model, with effects `θ₁` and
`θ₂`, and the two sets of studies are independent, then the indirect estimate
`θ̂_Y - θ̂_Z` is unbiased for `θ₁ - θ₂` with variance `1 / ∑ wᵢ + 1 / ∑ uⱼ`. -/
theorem indirectEstimate_ivwEstimate (hY : IsCommonEffectModel P Y θ₁ v)
    (hZ : IsCommonEffectModel P Z θ₂ u)
    (hind : IndepFun (fun ω i => Y i ω) (fun ω j => Z j ω) P) :
    ∫ ω, indirectEstimate (fun ω => ivwEstimate v fun i => Y i ω)
        (fun ω => ivwEstimate u fun j => Z j ω) ω ∂P = θ₁ - θ₂ ∧
      Var[indirectEstimate (fun ω => ivwEstimate v fun i => Y i ω)
          (fun ω => ivwEstimate u fun j => Z j ω); P] =
        1 / ∑ i, ivWeight v i + 1 / ∑ j, ivWeight u j := by
  have := hY.isProbabilityMeasure
  obtain ⟨hm1, hv1⟩ := hY.integral_variance_ivwEstimate
  obtain ⟨hm2, hv2⟩ := hZ.integral_variance_ivwEstimate
  have hind' : IndepFun (fun ω => ivwEstimate v fun i => Y i ω)
      (fun ω => ivwEstimate u fun j => Z j ω) P :=
    hind.comp (measurable_ivwEstimate v) (measurable_ivwEstimate u)
  refine ⟨?_, ?_⟩
  · simp only [indirectEstimate]
    rw [integral_sub (hY.memLp_ivwEstimate.integrable one_le_two)
      (hZ.memLp_ivwEstimate.integrable one_le_two), hm1, hm2]
  · rw [variance_indirectEstimate_of_indepFun hY.memLp_ivwEstimate hZ.memLp_ivwEstimate hind',
      hv1, hv2]

/-- **A concrete indirect comparison.** Three studies of `a` against `c` with the variances of
the example and two studies of `b` against `c` with variances `(1, 1)`, all independent Gaussian
(the product of `⊗ᵢ N(θ₁, vᵢ)` and `⊗ⱼ N(θ₂, 1)`): the indirect estimate is unbiased for
`θ₁ - θ₂` with variance `1/7 + 1/2`. -/
theorem indirectEstimate_ivwEstimate_example (θ₁ θ₂ : ℝ) :
    ∫ ω, indirectEstimate (fun ω => ivwEstimate exampleVar ω.1)
        (fun ω => ivwEstimate (fun _ : Fin 2 => (1 : ℝ)) ω.2) ω
        ∂((Measure.pi fun i => gaussianReal θ₁ (exampleVar i).toNNReal).prod
          (Measure.pi fun _ : Fin 2 => gaussianReal θ₂ (1 : ℝ).toNNReal)) = θ₁ - θ₂ ∧
      Var[indirectEstimate (fun ω => ivwEstimate exampleVar ω.1)
          (fun ω => ivwEstimate (fun _ : Fin 2 => (1 : ℝ)) ω.2);
        (Measure.pi fun i => gaussianReal θ₁ (exampleVar i).toNNReal).prod
          (Measure.pi fun _ : Fin 2 => gaussianReal θ₂ (1 : ℝ).toNNReal)] = 1 / 7 + 1 / 2 := by
  set μ := Measure.pi fun i => gaussianReal θ₁ (exampleVar i).toNNReal
  set ν := Measure.pi fun _ : Fin 2 => gaussianReal θ₂ (1 : ℝ).toNNReal
  have hY : IsCommonEffectModel (μ.prod ν) (fun i ω => ω.1 i) θ₁ exampleVar :=
    (isGaussianCommonEffectModel_of_hasLaw exampleVar_pos
      (measurePreserving_fst (μ := μ) (ν := ν)).hasLaw).isCommonEffectModel
  have hZ : IsCommonEffectModel (μ.prod ν) (fun j ω => ω.2 j) θ₂ fun _ : Fin 2 => (1 : ℝ) :=
    (isGaussianCommonEffectModel_of_hasLaw (fun _ => one_pos)
      (measurePreserving_snd (μ := μ) (ν := ν)).hasLaw).isCommonEffectModel
  have hind : IndepFun (fun ω : (Fin 3 → ℝ) × (Fin 2 → ℝ) => ω.1) (fun ω => ω.2) (μ.prod ν) :=
    indepFun_prod (X := id) (Y := id) measurable_id measurable_id
  have h := indirectEstimate_ivwEstimate hY hZ hind
  rw [example_sum_ivWeight] at h
  refine ⟨h.1, ?_⟩
  rw [h.2]
  norm_num [ivWeight]

end Indirect

end MetaAnalysis

end CausalInference
