/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.Estimation.LikelihoodTestsVector
public import CausalInference.Estimation.BernoulliPair
public import CausalInference.Estimation.BernoulliLikelihoodTests

/-!
# Two independent Bernoulli observations: the vector likelihood theory

For an i.i.d. sample from the two-parameter family `bernoulliPair` (a pair of independent
Bernoulli variables with success probabilities `θ₀ 0, θ₀ 1 ∈ (ε, 1 - ε)`), the estimator is the
pair of clipped coordinate sample means. Every hypothesis of the vector theorems is verified: the
score vector is the pair of the scalar Bernoulli scores, the score is regular on a closed ball
(`IsScoreRegularVec`, with an envelope from compactness), the information matrix
`diag(1 / (θ (1 - θ)))` is positive definite, the estimator is consistent, and it solves the
score equations with probability tending to one. The three tests of `θ = θ₀` then have the
chi-square limit with two degrees of freedom.

## Main definitions

* `CausalInference.ParametricFamily.bernoulliPairClip`: the pair of clipped sample means.

## Main results

* `CausalInference.ParametricFamily.bernoulliPair_scoreVec`: the score vector.
* `CausalInference.ParametricFamily.bernoulliPair_isScoreRegularVec`: score regularity.
* `CausalInference.ParametricFamily.bernoulliPair_clip_tendstoInDistribution`:
  `√n (θ̂_n - θ₀) → N(0, diag(θ₀ (1 - θ₀)))`.
* `CausalInference.ParametricFamily.bernoulliPair_clip_isAsymptoticallyEfficientVec` and, for
  one Bernoulli sample, `bernoulli_clip_isAsymptoticallyEfficient`.
* `CausalInference.ParametricFamily.bernoulliPair_clip_waldStatVec_tendstoInDistribution`
  (plug-in information), `bernoulliPair_scoreStatVec_tendstoInDistribution` and
  `bernoulliPair_clip_lrStatVec_tendstoInDistribution`: the Wald, score and likelihood ratio
  tests, each with limit `χ²₂`.

References: A. W. van der Vaart (1998), *Asymptotic Statistics*, chapters 5 and 16.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Finset Metric Matrix
open scoped Topology ENNReal NNReal

namespace CausalInference

namespace ParametricFamily

/-- The first marginal of the pair law is the Bernoulli law of the first parameter. -/
theorem bernoulliPair_law_map_fst {θ : Fin 2 → ℝ} (hθ : θ ∈ bernoulliPair.Θ) :
    (bernoulliPair.law θ).map Prod.fst = bernoulli.law (θ 0) := by
  have := isProbabilityMeasure_law hθ
  have h1 := isProbabilityMeasure_law (F := bernoulli) hθ.1
  refine Measure.ext_of_singleton fun b ↦ ?_
  rw [Measure.map_apply measurable_fst (measurableSet_singleton b),
    ← ENNReal.ofReal_toReal (measure_ne_top _ _),
    ← ENNReal.ofReal_toReal (measure_ne_top (bernoulli.law (θ 0)) _)]
  congr 1
  rw [← measureReal_def, ← measureReal_def,
    ← integral_indicator_one ((measurableSet_singleton b).preimage measurable_fst),
    ← integral_indicator_one (measurableSet_singleton b), bernoulliPair_integral_law hθ,
    bernoulli_integral_law hθ.1]
  cases b <;> simp [Set.indicator] <;> ring

/-- The second marginal of the pair law is the Bernoulli law of the second parameter. -/
theorem bernoulliPair_law_map_snd {θ : Fin 2 → ℝ} (hθ : θ ∈ bernoulliPair.Θ) :
    (bernoulliPair.law θ).map Prod.snd = bernoulli.law (θ 1) := by
  have := isProbabilityMeasure_law hθ
  have h1 := isProbabilityMeasure_law (F := bernoulli) hθ.2
  refine Measure.ext_of_singleton fun b ↦ ?_
  rw [Measure.map_apply measurable_snd (measurableSet_singleton b),
    ← ENNReal.ofReal_toReal (measure_ne_top _ _),
    ← ENNReal.ofReal_toReal (measure_ne_top (bernoulli.law (θ 1)) _)]
  congr 1
  rw [← measureReal_def, ← measureReal_def,
    ← integral_indicator_one ((measurableSet_singleton b).preimage measurable_snd),
    ← integral_indicator_one (measurableSet_singleton b), bernoulliPair_integral_law hθ,
    bernoulli_integral_law hθ.2]
  cases b <;> simp [Set.indicator] <;> ring

/-- **The score vector of the pair** is the pair of scalar Bernoulli scores. -/
theorem bernoulliPair_scoreVec {θ : Fin 2 → ℝ} (hθ : θ ∈ bernoulliPair.Θ) (x : Bool × Bool) :
    bernoulliPair.scoreVec θ x = ![bernoulli.score (θ 0) x.1, bernoulli.score (θ 1) x.2] := by
  have h0 := (bernoulli_density_pos hθ.1 x.1).ne'
  have h1 := (bernoulli_density_pos hθ.2 x.2).ne'
  funext j
  fin_cases j
  · simp only [scoreVec, Fin.zero_eta, bernoulliPair_partialDeriv_zero, bernoulliPair_density,
      Matrix.cons_val_zero, score, bernoulli_densityDeriv]
    rw [mul_div_mul_right _ _ h1]
  · simp only [scoreVec, Fin.mk_one, bernoulliPair_partialDeriv_one, bernoulliPair_density,
      Matrix.cons_val_one, score, bernoulli_densityDeriv]
    rw [mul_div_mul_left _ _ h0]
    rfl

/-- The radius `min (min θ₀ (1 - θ₀)) (min θ₁ (1 - θ₁))` of a ball around `θ ∈ Θ` inside `Θ`. -/
noncomputable def bernoulliPairRadius (θ : Fin 2 → ℝ) : ℝ :=
  min (min (θ 0) (1 - θ 0)) (min (θ 1) (1 - θ 1))

theorem bernoulliPairRadius_pos {θ : Fin 2 → ℝ} (hθ : θ ∈ bernoulliPair.Θ) :
    0 < bernoulliPairRadius θ :=
  lt_min (lt_min hθ.1.1 (by linarith [hθ.1.2])) (lt_min hθ.2.1 (by linarith [hθ.2.2]))

/-- **The score of the pair is regular** on the closed ball of radius half the radius
`bernoulliPairRadius θ₀`. The density is smooth and positive on the ball of that radius, and the
envelope of the Hessian entries comes from their continuity on a compact ball, the sample space
being finite. -/
theorem bernoulliPair_isScoreRegularVec {θ₀ : Fin 2 → ℝ} (hθ₀ : θ₀ ∈ bernoulliPair.Θ) :
    bernoulliPair.IsScoreRegularVec θ₀ (bernoulliPairRadius θ₀ / 2) := by
  have := isProbabilityMeasure_law hθ₀
  set ε := bernoulliPairRadius θ₀
  have hε : 0 < ε := bernoulliPairRadius_pos hθ₀
  have hball : ball θ₀ ε ⊆ bernoulliPair.Θ := ball_subset_bernoulliPair_Θ
  have hpos : ∀ η ∈ ball θ₀ ε, ∀ x, 0 < bernoulliPair.density η x := fun η hη x ↦
    mul_pos (bernoulli_density_pos (hball hη).1 _) (bernoulli_density_pos (hball hη).2 _)
  have hsub : closedBall θ₀ (ε / 2) ⊆ ball θ₀ ε := closedBall_subset_ball (by linarith)
  have hcont : ∀ x, ContinuousOn (fun u ↦ fun j k ↦ bernoulliPair.hessianLogLik j k u x)
      (closedBall θ₀ (ε / 2)) := fun x ↦ continuousOn_pi.2 fun j ↦ continuousOn_pi.2 fun k ↦
    (continuousOn_hessianLogLik_of_contDiffOn (contDiff_bernoulliPair_density x).contDiffOn
      (fun η hη ↦ hpos η hη x) j k).mono hsub
  have hbd : ∀ x, ∃ C, ∀ u ∈ closedBall θ₀ (ε / 2),
      ‖fun j k ↦ bernoulliPair.hessianLogLik j k u x‖ ≤ C := fun x ↦
    (isCompact_closedBall θ₀ (ε / 2)).exists_bound_of_continuousOn (hcont x)
  choose C hC using hbd
  refine IsScoreRegularVec.of_contDiffOn (half_pos hε) (by linarith)
    (ae_of_all _ fun x ↦ (contDiff_bernoulliPair_density x).contDiffOn)
    (ae_of_all _ fun x η hη ↦ hpos η hη x) .of_discrete (fun _ _ _ _ ↦ .of_discrete)
    (H := C) Integrable.of_finite (ae_of_all _ fun x u hu j k ↦ ?_)
  have h1 := norm_le_pi_norm (fun k ↦ bernoulliPair.hessianLogLik j k u x) k
  have h2 := norm_le_pi_norm (fun j k ↦ bernoulliPair.hessianLogLik j k u x) j
  rw [Real.norm_eq_abs] at h1
  exact h1.trans (h2.trans (hC x u hu))

/-- The inverse information matrix of the pair is `diag(θ₀ (1 - θ₀), θ₁ (1 - θ₁))`. -/
theorem bernoulliPair_inv_fisherInfoMatrix {θ : Fin 2 → ℝ} (hθ : θ ∈ bernoulliPair.Θ) :
    (bernoulliPair.fisherInfoMatrix θ)⁻¹ = diagonal ![θ 0 * (1 - θ 0), θ 1 * (1 - θ 1)] := by
  have a0 : θ 0 ≠ 0 := hθ.1.1.ne'
  have a1 : 1 - θ 0 ≠ 0 := by linarith [hθ.1.2]
  have b0 : θ 1 ≠ 0 := hθ.2.1.ne'
  have b1 : 1 - θ 1 ≠ 0 := by linarith [hθ.2.2]
  rw [bernoulliPair_fisherInfoMatrix hθ]
  refine inv_eq_left_inv ?_
  rw [diagonal_mul_diagonal, ← diagonal_one]
  congr 1
  ext i
  fin_cases i <;> simp <;> field_simp

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
  {O : ℕ → Ω → Bool × Bool} {ε : ℝ} {θ₀ : Fin 2 → ℝ}

/-- The pair of clipped coordinate sample means `max ε (min (1 - ε) p̂ⱼ)`. -/
noncomputable def bernoulliPairClip (ε : ℝ) (O : ℕ → Ω → Bool × Bool) (n : ℕ) (ω : Ω) :
    Fin 2 → ℝ :=
  ![max ε (min (1 - ε) (sampleMean successIndicator (fun i ω ↦ (O i ω).1) n ω)),
    max ε (min (1 - ε) (sampleMean successIndicator (fun i ω ↦ (O i ω).2) n ω))]

omit [IsProbabilityMeasure μ] in
/-- The clipped estimator lies in the parameter set. -/
theorem bernoulliPairClip_mem (hε : 0 < ε) (hε2 : ε ≤ 1 / 2) (n : ℕ) (ω : Ω) :
    bernoulliPairClip ε O n ω ∈ bernoulliPair.Θ := by
  have h : ∀ q : ℝ, max ε (min (1 - ε) q) ∈ Set.Ioo (0 : ℝ) 1 := fun q ↦
    ⟨lt_max_of_lt_left hε, max_lt (by linarith) ((min_le_left _ _).trans_lt (by linarith))⟩
  exact ⟨h _, h _⟩

omit [IsProbabilityMeasure μ] in
/-- The clipped estimator is measurable. -/
theorem aemeasurable_bernoulliPairClip (hO : IsIIDSample O μ) (n : ℕ) :
    AEMeasurable (bernoulliPairClip ε O n) μ := by
  refine aemeasurable_pi_iff.2 fun j ↦ ?_
  fin_cases j
  · exact aemeasurable_bernoulli_clip (hO.comp measurable_fst) n
  · exact aemeasurable_bernoulli_clip (hO.comp measurable_snd) n

omit [IsProbabilityMeasure μ] in
/-- The marginal samples have Bernoulli laws. -/
theorem map_fst_snd_eq (hO : IsIIDSample O μ) (hθ₀ : θ₀ ∈ bernoulliPair.Θ)
    (hlaw : μ.map (O 0) = bernoulliPair.law θ₀) :
    μ.map (fun ω ↦ (O 0 ω).1) = bernoulli.law (θ₀ 0) ∧
      μ.map (fun ω ↦ (O 0 ω).2) = bernoulli.law (θ₀ 1) := by
  constructor
  · rw [← bernoulliPair_law_map_fst hθ₀, ← hlaw,
      AEMeasurable.map_map_of_aemeasurable measurable_fst.aemeasurable (hO.aemeasurable 0)]
    rfl
  · rw [← bernoulliPair_law_map_snd hθ₀, ← hlaw,
      AEMeasurable.map_map_of_aemeasurable measurable_snd.aemeasurable (hO.aemeasurable 0)]
    rfl

variable (hε : 0 < ε) (hε2 : ε ≤ 1 / 2) (hO : IsIIDSample O μ)
  (hθ₀ : ∀ j, θ₀ j ∈ Set.Ioo ε (1 - ε)) (hlaw : μ.map (O 0) = bernoulliPair.law θ₀)

include hε hθ₀ in
omit [IsProbabilityMeasure μ] in
/-- A parameter with coordinates in `(ε, 1 - ε)` lies in `Θ`. -/
theorem mem_bernoulliPair_Θ_of_eps : θ₀ ∈ bernoulliPair.Θ :=
  ⟨mem_Ioo_of_mem_Ioo_eps hε (hθ₀ 0), mem_Ioo_of_mem_Ioo_eps hε (hθ₀ 1)⟩

include hε hε2 hO hθ₀ hlaw

/-- **The clipped estimator is consistent.** -/
theorem bernoulliPairClip_tendstoInMeasure :
    TendstoInMeasure μ (bernoulliPairClip ε O) atTop (fun _ ↦ θ₀) := by
  have hm := map_fst_snd_eq hO (mem_bernoulliPair_Θ_of_eps hε hθ₀) hlaw
  refine tendstoInMeasure_pi (X := fun j n ω ↦ bernoulliPairClip ε O n ω j) fun j ↦ ?_
  fin_cases j
  · exact bernoulli_clip_isConsistent hε hε2 (hO.comp measurable_fst)
      ⟨(hθ₀ 0).1.le, (hθ₀ 0).2.le⟩ hm.1
  · exact bernoulli_clip_isConsistent hε hε2 (hO.comp measurable_snd)
      ⟨(hθ₀ 1).1.le, (hθ₀ 1).2.le⟩ hm.2

/-- **The clipped estimator solves the score equations** with probability tending to one. -/
theorem bernoulliPairClip_root :
    WithProbTendingToOne μ (fun n ↦ {ω | ∑ i ∈ range n,
      bernoulliPair.scoreVec (bernoulliPairClip ε O n ω) (O i ω) = 0}) := by
  have hm := map_fst_snd_eq hO (mem_bernoulliPair_Θ_of_eps hε hθ₀) hlaw
  refine ((bernoulli_clip_root hε hε2 (hO.comp measurable_fst) (hθ₀ 0) hm.1).inter
    (bernoulli_clip_root hε hε2 (hO.comp measurable_snd) (hθ₀ 1) hm.2)).mono fun n ω hω ↦ ?_
  obtain ⟨h1, h2⟩ := hω
  simp only [Set.mem_ofPred_eq] at h1 h2 ⊢
  simp_rw [bernoulliPair_scoreVec (bernoulliPairClip_mem hε hε2 n ω)]
  funext j
  fin_cases j
  · simpa [Finset.sum_apply, bernoulliPairClip] using h1
  · simpa [Finset.sum_apply, bernoulliPairClip] using h2

/-- **Asymptotic normality of the clipped estimator of the pair**:
`√n (θ̂_n - θ₀) → N(0, diag(θ₀ (1 - θ₀), θ₁ (1 - θ₁)))`, the inverse information, by
`mle_tendstoInDistribution_vec` with every hypothesis discharged. -/
theorem bernoulliPair_clip_tendstoInDistribution {Ω' : Type*} {mΩ' : MeasurableSpace Ω'}
    {P' : Measure Ω'} [IsProbabilityMeasure P'] {Y : Ω' → EuclideanSpace ℝ (Fin 2)}
    (hY : HasLaw Y (multivariateGaussian 0
      (diagonal ![θ₀ 0 * (1 - θ₀ 0), θ₀ 1 * (1 - θ₀ 1)])) P') :
    TendstoInDistribution (fun (n : ℕ) ω ↦ √(n : ℝ) •
      (WithLp.toLp 2 (bernoulliPairClip ε O n ω) - WithLp.toLp 2 θ₀ :
        EuclideanSpace ℝ (Fin 2))) atTop Y (fun _ ↦ μ) P' := by
  have hθ := mem_bernoulliPair_Θ_of_eps hε hθ₀
  refine mle_tendstoInDistribution_vec hO hlaw (bernoulliPair_isRegularAtVec hθ)
    (bernoulliPair_isScoreRegularVec hθ) (bernoulliPair_fisherInfoMatrix_posDef hθ)
    (aemeasurable_bernoulliPairClip hO) (bernoulliPairClip_tendstoInMeasure hε hε2 hO hθ₀ hlaw)
    (bernoulliPairClip_root hε hε2 hO hθ₀ hlaw) ?_
  rwa [bernoulliPair_inv_fisherInfoMatrix hθ]

/-- **The clipped estimator of the pair is asymptotically efficient.** -/
theorem bernoulliPair_clip_isAsymptoticallyEfficientVec :
    bernoulliPair.IsAsymptoticallyEfficientVec (bernoulliPairClip ε O) θ₀ μ := by
  have hθ := mem_bernoulliPair_Θ_of_eps hε hθ₀
  exact mle_isAsymptoticallyEfficientVec hO hlaw (bernoulliPair_isRegularAtVec hθ)
    (bernoulliPair_isScoreRegularVec hθ) (bernoulliPair_fisherInfoMatrix_posDef hθ)
    (aemeasurable_bernoulliPairClip hO) (bernoulliPairClip_tendstoInMeasure hε hε2 hO hθ₀ hlaw)
    (bernoulliPairClip_root hε hε2 hO hθ₀ hlaw)

/-- **The Wald test for the pair, with the plug-in information** `I(θ̂_n)`: the statistic
`n (θ̂_n - θ₀)ᵀ I(θ̂_n) (θ̂_n - θ₀)` converges in distribution to `χ²₂`. -/
theorem bernoulliPair_clip_waldStatVec_tendstoInDistribution {Ω'' : Type*}
    {mΩ'' : MeasurableSpace Ω''} {P'' : Measure Ω''} [IsProbabilityMeasure P''] {W : Ω'' → ℝ}
    (hW : HasLaw W (chiSquared 2) P'') :
    TendstoInDistribution (waldStatVec (bernoulliPairClip ε O) θ₀
      (fun n ω ↦ bernoulliPair.fisherInfoMatrix (bernoulliPairClip ε O n ω))) atTop W
      (fun _ ↦ μ) P'' := by
  have hθ := mem_bernoulliPair_Θ_of_eps hε hθ₀
  set g : (Fin 2 → ℝ) → Matrix (Fin 2) (Fin 2) ℝ := fun θ ↦
    diagonal ![1 / (θ 0 * (1 - θ 0)), 1 / (θ 1 * (1 - θ 1))] with hg
  have hIh : (fun n ω ↦ bernoulliPair.fisherInfoMatrix (bernoulliPairClip ε O n ω)) =
      fun n ω ↦ g (bernoulliPairClip ε O n ω) := by
    funext n ω
    exact bernoulliPair_fisherInfoMatrix (bernoulliPairClip_mem hε hε2 n ω)
  have hN := bernoulliPair_clip_tendstoInDistribution hε hε2 hO hθ₀ hlaw (Y := id) HasLaw.id
  have hY : HasLaw (id : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2))
      (multivariateGaussian 0 (bernoulliPair.fisherInfoMatrix θ₀)⁻¹)
      (multivariateGaussian 0 (diagonal ![θ₀ 0 * (1 - θ₀ 0), θ₀ 1 * (1 - θ₀ 1)])) := by
    rw [bernoulliPair_inv_fisherInfoMatrix hθ]; exact HasLaw.id
  have h0 : θ₀ 0 * (1 - θ₀ 0) ≠ 0 := mul_ne_zero hθ.1.1.ne' (by linarith [hθ.1.2])
  have h1 : θ₀ 1 * (1 - θ₀ 1) ≠ 0 := mul_ne_zero hθ.2.1.ne' (by linarith [hθ.2.2])
  have hgc : ContinuousAt g θ₀ := by
    refine Continuous.continuousAt (f := diagonal) continuous_id.matrix_diagonal |>.comp ?_
    refine continuousAt_pi.2 (Fin.forall_fin_two.2 ⟨?_, ?_⟩)
    · simp only [cons_val_zero]
      exact continuousAt_const.div
        (by fun_prop : ContinuousAt (fun θ : Fin 2 → ℝ ↦ θ 0 * (1 - θ 0)) θ₀) h0
    · simp only [cons_val_one]
      exact continuousAt_const.div
        (by fun_prop : ContinuousAt (fun θ : Fin 2 → ℝ ↦ θ 1 * (1 - θ 1)) θ₀) h1
  have hcont : ∀ j k, ContinuousAt (fun θ ↦ g θ j k) θ₀ := fun j k ↦
    (continuous_id.matrix_elem j k).continuousAt.comp hgc
  have hmeas : ∀ j k, Measurable (fun θ ↦ g θ j k) := by
    intro j k
    simp only [hg, diagonal_apply]
    split_ifs with hjk
    · subst hjk
      revert j
      refine Fin.forall_fin_two.2 ⟨?_, ?_⟩
      · simp only [cons_val_zero]; fun_prop
      · simp only [cons_val_one]; fun_prop
    · exact measurable_const
  rw [hIh]
  refine waldStatVec_tendstoInDistribution (bernoulliPair_fisherInfoMatrix_posDef hθ) hY hN
    (fun j k ↦ ?_) (fun n j k ↦ (hmeas j k).comp_aemeasurable
      (aemeasurable_bernoulliPairClip hO n)) hW
  have h := (bernoulliPairClip_tendstoInMeasure hε hε2 hO hθ₀ hlaw).comp_continuousAt (hcont j k)
  rwa [bernoulliPair_fisherInfoMatrix hθ]

omit hε2 in
/-- **The score test for the pair**: `R_n → χ²₂` in distribution. -/
theorem bernoulliPair_scoreStatVec_tendstoInDistribution
    {Ω'' : Type*} {mΩ'' : MeasurableSpace Ω''} {P'' : Measure Ω''} [IsProbabilityMeasure P'']
    {W : Ω'' → ℝ} (hW : HasLaw W (chiSquared 2) P'') :
    TendstoInDistribution (bernoulliPair.scoreStatVec O θ₀) atTop W (fun _ ↦ μ) P'' := by
  have hθ := mem_bernoulliPair_Θ_of_eps hε hθ₀
  exact scoreStatVec_tendstoInDistribution hO hlaw (bernoulliPair_isRegularAtVec hθ)
    .of_discrete (bernoulliPair_fisherInfoMatrix_posDef hθ) hW

omit hε hε2 hO hθ₀ hlaw in
/-- The log-likelihood of the pair is jointly measurable. -/
theorem measurable_bernoulliPair_logLik :
    Measurable fun q : (Fin 2 → ℝ) × (Bool × Bool) ↦ bernoulliPair.logLik q.1 q.2 := by
  refine measurable_from_prod_countable_left fun x ↦ ?_
  rcases x with ⟨_ | _, _ | _⟩ <;>
    simp only [logLik, bernoulliPair_density, bernoulli_density, Bool.false_eq_true, ite_true,
      ite_false] <;> fun_prop

/-- **Wilks' theorem for the pair**: the likelihood ratio statistic of the clipped estimator
converges in distribution to `χ²₂`. -/
theorem bernoulliPair_clip_lrStatVec_tendstoInDistribution {Ω'' : Type*}
    {mΩ'' : MeasurableSpace Ω''} {P'' : Measure Ω''} [IsProbabilityMeasure P''] {W : Ω'' → ℝ}
    (hW : HasLaw W (chiSquared 2) P'') :
    TendstoInDistribution (bernoulliPair.lrStatVec O (bernoulliPairClip ε O) θ₀) atTop W
      (fun _ ↦ μ) P'' := by
  have hθ := mem_bernoulliPair_Θ_of_eps hε hθ₀
  exact lrStatVec_tendstoInDistribution hO hlaw (bernoulliPair_isRegularAtVec hθ)
    (bernoulliPair_isScoreRegularVec hθ) (bernoulliPair_fisherInfoMatrix_posDef hθ)
    measurable_bernoulliPair_logLik (aemeasurable_bernoulliPairClip hO)
    (bernoulliPairClip_tendstoInMeasure hε hε2 hO hθ₀ hlaw)
    (bernoulliPairClip_root hε hε2 hO hθ₀ hlaw) hW

omit hε hε2 hO hθ₀ hlaw in
/-- **The clipped Bernoulli estimator is asymptotically efficient**, for one Bernoulli sample
with success probability `p₀ ∈ (ε, 1 - ε)`. -/
theorem bernoulli_clip_isAsymptoticallyEfficient (hε : 0 < ε) (hε2 : ε ≤ 1 / 2)
    {X : ℕ → Ω → Bool} (hX : IsIIDSample X μ) {p₀ : ℝ} (hp₀ : p₀ ∈ Set.Ioo ε (1 - ε))
    (hlaw : μ.map (X 0) = bernoulli.law p₀) :
    bernoulli.IsAsymptoticallyEfficient
      (fun n ω ↦ max ε (min (1 - ε) (sampleMean successIndicator X n ω))) p₀ μ := by
  have hp := mem_Ioo_of_mem_Ioo_eps hε hp₀
  exact mle_isAsymptoticallyEfficient hX hlaw (bernoulli_isRegularAt hp)
    (bernoulli_isScoreRegular hp) (bernoulli_fisherInfo_pos hp) (aemeasurable_bernoulli_clip hX)
    (bernoulli_clip_isConsistent hε hε2 hX ⟨hp₀.1.le, hp₀.2.le⟩ hlaw)
    (bernoulli_clip_root hε hε2 hX hp₀ hlaw)

end ParametricFamily

end CausalInference
