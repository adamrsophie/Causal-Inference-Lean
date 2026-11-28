/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.NetworkMetaRegression.AggregateCountExposure
public import CausalInference.NetworkMetaRegression.AggregateCountExamples
public import CausalInference.NetworkMetaRegression.LogitCounterexample
public import CausalInference.NetworkMetaRegression.Examples

/-!
# Aggregate counts: instances of the general theorems

Every hypothesis is discharged and the values are computed.

* **Generating functions** on `Bin(2, 1/2)`, with generating function `(1/2 + z/2)²`: the second
  derivative at `0` by `hasDerivAt_iteratedDeriv_generatingFunction`, the masses `1/2` and `1/4`
  of `1` and `2` from the derivatives at `0`, the factorial moments `E N = 1` and
  `E N(N - 1) = 1/2` from the derivatives at `1` (both directions). On the Poisson law: the sum
  of independent `Po(1)` and `Po(2)` counts is `Po(3)` (product rule and uniqueness).
* **The binomial likelihood** on the logit triangle model at baseline `0`, covariate law
  `binaryLaw (1/2)`: risks `1/2`, `6/7`, arm mean `19/28`; the count of an arm of two patients
  equals `1` with probability `171/392`, which is the aggregate likelihood factor.
* **The log link** on the same model with `exp`: rates `1` and `6`, arm mean `7/2`, rate
  variance `25/4`; the count of `n` patients has mean `7n/2` and variance `7n/2 + 25n/4`; with a
  point mass covariate law the count is equidispersed; under a standard Gaussian covariate the
  variance is `n e^{v/2} + n e^{v} (e^{v} - 1)`, `v = (log 6)²`.
* **The mixed Poisson mass**: with rates `3`, `1` under `bernoulliLaw (1/2)`, two patients have
  no event with probability `((e^{-3} + e^{-1})/2)²`.
* **Exposures** `1` and `2` with rates `3`, `1`: mean `6`, variance `11`; with the log offset on
  the model above: mean `21/2`, variance `167/4`.
* **A three category multinomial law** `Multinomial(6; 1/2, 1/3, 1/6)`: the first count is
  `Bin(6, 1/2)`, `E n₂ = 2`, `Cov(n₁, n₂) = -1`, `Var n₃ = 5/6`.
* **The binomial density**: `log P_{Bin(2,1/2)}(1) = log 2 + ℓ(2, 1, 1/2) = -log 2`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set Filter Topology CausalInference.EffectMeasure
  CausalInference.NetworkMetaAnalysis CausalInference.IndirectComparison
open scoped unitInterval ENNReal NNReal

namespace CausalInference

namespace NetworkMetaRegression

namespace AggregateCountInstance

/-! ### Generating functions -/

/-- The parameter `1/2` of the unit interval. -/
noncomputable def half : I := ⟨1 / 2, by norm_num, by norm_num⟩

theorem generatingFunction_binomial_half (z : ℝ) :
    generatingFunction (Bin(2, half)) z = (1 / 2 + z / 2) ^ 2 := by
  rw [← poissonBinomial_const, generatingFunction_poissonBinomial]
  simp only [half, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  ring

theorem generatingFunction_binomial_half_eq :
    generatingFunction (Bin(2, half)) = fun z => (1 / 2 + z / 2) ^ 2 :=
  funext generatingFunction_binomial_half

theorem iteratedDeriv_one_binomial_half :
    iteratedDeriv 1 (generatingFunction (Bin(2, half))) = fun z => 1 / 2 + z / 2 := by
  rw [iteratedDeriv_one, generatingFunction_binomial_half_eq]
  funext z
  refine HasDerivAt.deriv ?_
  have h := ((hasDerivAt_id z).div_const 2).const_add (1 / 2)
  convert h.mul h using 1
  · funext x; simp only [id, Pi.mul_apply]; ring
  · simp only [id]; ring

/-- **The second derivative at `0` from the derivative theorem**: `G''(0) = 1/2`. -/
theorem iteratedDeriv_two_binomial_half :
    iteratedDeriv 2 (generatingFunction (Bin(2, half))) 0 = 1 / 2 := by
  have h := hasDerivAt_iteratedDeriv_generatingFunction (ν := Bin(2, half)) 1
    (z := 0) (by norm_num)
  rw [iteratedDeriv_one_binomial_half] at h
  have h' : HasDerivAt (fun z : ℝ => 1 / 2 + z / 2) (1 / 2) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).div_const 2).const_add (1 / 2)
  exact h.unique h'

/-- **The masses from the derivatives at `0`**: `P(N = 1) = 1/2`, `P(N = 2) = 1/4`. -/
theorem measureReal_binomial_half :
    (Bin(2, half)).real {1} = 1 / 2 ∧ (Bin(2, half)).real {2} = 1 / 4 := by
  refine ⟨?_, ?_⟩
  · rw [measureReal_singleton_eq_iteratedDeriv, iteratedDeriv_one_binomial_half]
    norm_num
  · rw [measureReal_singleton_eq_iteratedDeriv, iteratedDeriv_two_binomial_half]
    norm_num [Nat.factorial]

/-- **The factorial moments from the derivatives at `1`**: `E N = 1` and `E N(N - 1) = 1/2`,
with integrability, from the left limits of `G'` and `G''` at `1`; the limit of `G''` at `1`
is then recovered from the integrable second factorial moment. -/
theorem factorialMoments_binomial_half :
    ∫ k, (k.descFactorial 1 : ℝ) ∂Bin(2, half) = 1 ∧
      ∫ k, (k.descFactorial 2 : ℝ) ∂Bin(2, half) = 1 / 2 ∧
      Tendsto (iteratedDeriv 2 (generatingFunction (Bin(2, half)))) (𝓝[<] 1) (𝓝 (1 / 2)) := by
  have hd2 : iteratedDeriv 2 (generatingFunction (Bin(2, half))) = fun _ => 1 / 2 := by
    rw [iteratedDeriv_succ, iteratedDeriv_one_binomial_half]
    funext z
    refine HasDerivAt.deriv ?_
    simpa using ((hasDerivAt_id z).div_const 2).const_add (1 / 2)
  have h1 : Tendsto (iteratedDeriv 1 (generatingFunction (Bin(2, half)))) (𝓝[<] 1) (𝓝 1) := by
    rw [iteratedDeriv_one_binomial_half]
    have : Continuous fun z : ℝ => 1 / 2 + z / 2 := by fun_prop
    have h := (this.tendsto 1).mono_left (nhdsWithin_le_nhds (s := Iio 1))
    norm_num at h ⊢
    exact h
  have h2 : Tendsto (iteratedDeriv 2 (generatingFunction (Bin(2, half)))) (𝓝[<] 1)
      (𝓝 (1 / 2)) := by
    rw [hd2]; exact tendsto_const_nhds
  obtain ⟨-, e1⟩ := integrable_descFactorial_of_tendsto 1 h1
  obtain ⟨i2, e2⟩ := integrable_descFactorial_of_tendsto 2 h2
  refine ⟨e1, e2, ?_⟩
  have := tendsto_iteratedDeriv_generatingFunction 2 i2
  rwa [e2] at this

/-- **The sum of independent `Po(1)` and `Po(2)` counts is `Po(3)`**, by the product rule and the
uniqueness of the generating function. -/
theorem map_add_poisson_one_two :
    ((poissonMeasure 1).prod (poissonMeasure 2)).map (fun ω => ω.1 + ω.2) = poissonMeasure 3 := by
  refine eq_of_generatingFunction_eqOn fun z hz => ?_
  have hz' : |z| ≤ 1 := (abs_lt.mpr hz).le
  rw [(generatingFunction_map_add measurable_fst measurable_snd
    (indepFun_prod (X := id) (Y := id) measurable_id measurable_id) hz').2,
    Measure.map_fst_prod, Measure.map_snd_prod]
  simp only [measure_univ, one_smul]
  rw [generatingFunction_poissonMeasure _ hz', generatingFunction_poissonMeasure _ hz',
    generatingFunction_poissonMeasure _ hz', ← Real.exp_add]
  push_cast
  ring_nf

/-! ### The binomial likelihood on the logit triangle model -/

theorem sigmoid_mem (y : ℝ) : Real.sigmoid y ∈ I :=
  ⟨(Real.sigmoid_pos y).le, Real.sigmoid_le_one y⟩

instance : IsProbabilityMeasure (binaryLaw (1 / 2)) :=
  isProbabilityMeasure_binaryLaw ⟨by norm_num, by norm_num⟩

theorem surface_logitTriangle_zero (ginv : ℝ → ℝ) (b : ℝ) :
    logitTriangle.surface ginv 0 0 (fun _ => b) = ginv (b * Real.log 6) := by
  rw [MultilevelModel.surface, logitTriangle_eta]
  simp [logitTriangle, triangleModel]

theorem armMean_logitTriangle_sigmoid :
    logitTriangle.armMean Real.sigmoid 0 (binaryLaw (1 / 2)) 0 = 19 / 28 := by
  rw [MultilevelModel.armMean, integral_binaryLaw ⟨by norm_num, by norm_num⟩,
    surface_logitTriangle_zero, surface_logitTriangle_zero]
  have e1 : Real.exp (0 * Real.log 6) = 1 := by simp
  have e2 : Real.exp (1 * Real.log 6) = 6 := by rw [one_mul, Real.exp_log (by norm_num)]
  rw [sigmoid_eq_div_of_exp_eq e1, sigmoid_eq_div_of_exp_eq e2]
  norm_num

/-- The two study covariate laws, both `binaryLaw (1/2)`. -/
noncomputable def covLaws : Fin 2 → Measure (Fin 1 → ℝ) := fun _ => binaryLaw (1 / 2)

instance (j : Fin 2) : IsProbabilityMeasure (covLaws j) :=
  isProbabilityMeasure_binaryLaw ⟨by norm_num, by norm_num⟩

/-- The arm `(0, 0)` of the network in which every study has every treatment. -/
def arm00 : ArmIndex (fun _ : Fin 2 => (Finset.univ : Finset (Fin 3))) :=
  ⟨(0, 0), Finset.mem_univ _⟩

/-- **The binomial likelihood instance**: the aggregate record "one event among two patients" of
arm `(0, 0)` has likelihood factor `171/392 = 2 · (19/28) · (9/28)`. -/
theorem likelihood_binomialDensity_logitTriangle (f : ℝ → ℝ → ℝ) :
    logitTriangle.likelihood f (binomialDensity 2) Real.sigmoid covLaws [] [(arm00, (1 : ℕ))] =
      ENNReal.ofReal (171 / 392) := by
  rw [MultilevelModel.likelihood_cons_binomialDensity
    (by fun_prop : Continuous Real.sigmoid).measurable
    sigmoid_mem, MultilevelModel.likelihood_nil]
  rw [show {z : Fin 2 → (Fin 1 → ℝ) × ℕ | ∑ i, (z i).2 = 1} = (fun z => ∑ i, (z i).2) ⁻¹' {1}
      from rfl, ← map_measureReal_apply (by fun_prop) (measurableSet_singleton 1)]
  rw [MultilevelModel.map_sum_pi_compProd_eq_binomial
    (by fun_prop : Continuous Real.sigmoid).measurable
    sigmoid_mem, binomial_real_singleton]
  simp only [List.map_nil, List.prod_nil, mul_one, arm00, covLaws]
  have hμ : logitTriangle.μ 0 = 0 := by simp [logitTriangle, triangleModel]
  simp only [hμ, armMean_logitTriangle_sigmoid]
  norm_num

/-! ### The log link on the triangle model -/

theorem memLp_binaryLaw (g : (Fin 1 → ℝ) → ℝ) : MemLp g 2 (binaryLaw (1 / 2)) := by
  unfold binaryLaw twoAtomLaw
  exact ((memLp_dirac eNorm_lt_top).smul_measure ENNReal.ofReal_ne_top).add_measure
    ((memLp_dirac eNorm_lt_top).smul_measure ENNReal.ofReal_ne_top)

theorem armMean_logitTriangle_exp :
    logitTriangle.armMean Real.exp 0 (binaryLaw (1 / 2)) 0 = 7 / 2 := by
  rw [MultilevelModel.armMean, integral_binaryLaw ⟨by norm_num, by norm_num⟩,
    surface_logitTriangle_zero, surface_logitTriangle_zero, one_mul, Real.exp_log (by norm_num)]
  norm_num

theorem variance_surface_logitTriangle_exp :
    variance (logitTriangle.surface Real.exp 0 0) (binaryLaw (1 / 2)) = 25 / 4 := by
  rw [variance_eq_sub (memLp_binaryLaw _)]
  change _ - (logitTriangle.armMean Real.exp 0 (binaryLaw (1 / 2)) 0) ^ 2 = _
  rw [armMean_logitTriangle_exp]
  simp only [Pi.pow_apply]
  rw [integral_binaryLaw ⟨by norm_num, by norm_num⟩, surface_logitTriangle_zero,
    surface_logitTriangle_zero, one_mul, Real.exp_log (by norm_num)]
  norm_num

/-- **The log link count instance**: the count of `n` patients has mean `7n/2` and variance
`7n/2 + 25n/4`. -/
theorem count_logitTriangle_exp (n : ℕ) :
    ∫ z, ((∑ i, (z i).2 : ℕ) : ℝ) ∂(Measure.pi fun _ : Fin n => binaryLaw (1 / 2) ⊗ₘ
        poissonKernel _ (logitTriangle.measurable_surface Real.measurable_exp 0 0)) = 7 * n / 2 ∧
      variance (fun z => ((∑ i, (z i).2 : ℕ) : ℝ)) (Measure.pi fun _ : Fin n =>
        binaryLaw (1 / 2) ⊗ₘ
          poissonKernel _ (logitTriangle.measurable_surface Real.measurable_exp 0 0)) =
        7 * n / 2 + 25 * n / 4 := by
  refine ⟨?_, ?_⟩
  · rw [MultilevelModel.integral_count_poisson Real.measurable_exp (fun y => (Real.exp_pos y).le)
      _ _ _ ((memLp_binaryLaw _).integrable one_le_two), armMean_logitTriangle_exp]
    ring
  · rw [MultilevelModel.variance_count_poisson Real.measurable_exp (fun y => (Real.exp_pos y).le)
      _ _ _ (memLp_binaryLaw _), armMean_logitTriangle_exp, variance_surface_logitTriangle_exp]
    ring

/-- **The equidispersion instance**: under a point mass covariate law, the variance of the count
of `n ≥ 1` patients equals its mean. -/
theorem count_logitTriangle_dirac {n : ℕ} (hn : 0 < n) :
    variance (fun z => ((∑ i, (z i).2 : ℕ) : ℝ)) (Measure.pi fun _ : Fin n =>
        Measure.dirac (fun _ : Fin 1 => (0 : ℝ)) ⊗ₘ
          poissonKernel _ (logitTriangle.measurable_surface Real.measurable_exp 0 0)) =
      n * logitTriangle.armMean Real.exp 0 (Measure.dirac fun _ => 0) 0 := by
  refine (MultilevelModel.variance_count_poisson_eq_iff Real.measurable_exp
    (fun y => (Real.exp_pos y).le) _ _ _ (memLp_dirac eNorm_lt_top) hn).2 ?_
  rw [Filter.EventuallyEq, ae_dirac_eq, Filter.eventually_pure, MultilevelModel.armMean,
    integral_dirac]

/-- **The Gaussian instance**: with a standard Gaussian covariate the count of `n` patients has
variance `n e^{v/2} + n e^{v} (e^{v} - 1)`, `v = (log 6)²`. -/
theorem count_logitTriangle_gaussian (n : ℕ) :
    variance (fun z => ((∑ i, (z i).2 : ℕ) : ℝ)) (Measure.pi fun _ : Fin n =>
        stdGaussianLaw ⊗ₘ
          poissonKernel _ (logitTriangle.measurable_surface Real.measurable_exp 0 0)) =
      n * Real.exp (Real.log 6 ^ 2 / 2) +
        n * Real.exp (Real.log 6 ^ 2) * (Real.exp (Real.log 6 ^ 2) - 1) := by
  have hv : slopeVar stdGaussianLaw (logitTriangle.β₁ + logitTriangle.β₂ 0) = Real.log 6 ^ 2 := by
    rw [slopeVar_stdGaussianLaw]
    simp [logitTriangle, triangleModel]
  have hθ : logitTriangle.armMean Real.exp 0 stdGaussianLaw 0 = Real.exp (Real.log 6 ^ 2 / 2) := by
    rw [MultilevelModel.armMean_exp_gaussian, hv, covMean_stdGaussianLaw,
      show (0 : Fin 1 → ℝ) = fun _ => 0 from rfl, logitTriangle_eta]
    simp [logitTriangle, triangleModel]
  rw [MultilevelModel.variance_count_exp_gaussian, hv, hθ, ← Real.exp_nat_mul]
  push_cast
  ring_nf

/-! ### The mixed Poisson mass -/

open AggregateCountExample in
/-- **The mixed Poisson mass instance**: with rates `3` and `1` under `bernoulliLaw (1/2)`, two
patients have no event with probability `((e^{-3} + e^{-1})/2)²`. -/
theorem countArm_measureReal_zero :
    countArm.real {z | ∑ i, (z i).2 = 0} = ((Real.exp (-3) + Real.exp (-1)) / 2) ^ 2 := by
  rw [countArm, measureReal_count_pi_compProd_poissonKernel rate_nonneg]
  simp only [pow_zero, mul_one, Nat.factorial_zero, Nat.cast_one, div_one, ← Finset.sum_neg_distrib,
    Real.exp_sum]
  rw [integral_fintype_prod_eq_prod (fun _ b => Real.exp (-rate b)), Fin.prod_univ_two,
    integral_bernoulliLaw (by norm_num) (by norm_num)]
  norm_num [rate]
  ring

/-! ### Exposures -/

open AggregateCountExample in
/-- **The exposure instance**: exposures `1` and `2` and rates `3`, `1` under `bernoulliLaw (1/2)`
give a count with mean `6` and variance `11`. -/
theorem exposureArm_moments :
    ∫ w, ((∑ i, (w i).2 : ℕ) : ℝ)
        ∂exposureArm (bernoulliLaw (1 / 2)) rate Measurable.of_discrete ![1, 2] = 6 ∧
      variance (fun w => ((∑ i, (w i).2 : ℕ) : ℝ))
        (exposureArm (bernoulliLaw (1 / 2)) rate Measurable.of_discrete ![1, 2]) = 11 := by
  have he : ∀ i, (0 : ℝ) ≤ ![1, 2] i := fun i => by fin_cases i <;> norm_num
  have hE : ∫ b, rate b ∂bernoulliLaw (1 / 2) = 2 := by
    rw [integral_bernoulliLaw (by norm_num) (by norm_num)]; norm_num [rate]
  have hV : variance rate (bernoulliLaw (1 / 2)) = 1 := by
    rw [variance_eq_sub memLp_rate, hE]
    simp only [Pi.pow_apply]
    rw [integral_bernoulliLaw (by norm_num) (by norm_num)]; norm_num [rate]
  refine ⟨?_, ?_⟩
  · rw [integral_count_exposure rate_nonneg he (memLp_rate.integrable one_le_two), hE,
      Fin.sum_univ_two]
    norm_num
  · rw [variance_count_exposure rate_nonneg he memLp_rate, hE, hV, Fin.sum_univ_two,
      Fin.sum_univ_two]
    norm_num

/-- **The log offset instance**: on the triangle model with `exp`, exposures `1` and `2` give a
count with mean `21/2` and variance `167/4`. -/
theorem offsetArm_logitTriangle :
    ∫ w, ((∑ i, (w i).2 : ℕ) : ℝ) ∂logitTriangle.offsetArm 0 0 (binaryLaw (1 / 2)) ![1, 2] =
        21 / 2 ∧
      variance (fun w => ((∑ i, (w i).2 : ℕ) : ℝ))
        (logitTriangle.offsetArm 0 0 (binaryLaw (1 / 2)) ![1, 2]) = 167 / 4 := by
  have he : ∀ i, (0 : ℝ) < ![1, 2] i := fun i => by fin_cases i <;> norm_num
  refine ⟨?_, ?_⟩
  · rw [MultilevelModel.integral_count_offset _ _ _ he ((memLp_binaryLaw _).integrable one_le_two),
      armMean_logitTriangle_exp, Fin.sum_univ_two]
    norm_num
  · rw [MultilevelModel.variance_count_offset _ _ _ he (memLp_binaryLaw _),
      armMean_logitTriangle_exp, variance_surface_logitTriangle_exp, Fin.sum_univ_two,
      Fin.sum_univ_two]
    norm_num

/-! ### A three category multinomial law -/

/-- The category probabilities `1/2, 1/3, 1/6`. -/
noncomputable def threeProb : Fin 3 → ℝ := ![1 / 2, 1 / 3, 1 / 6]

theorem isWeights_threeProb : IsWeights threeProb := by
  refine ⟨fun k => by fin_cases k <;> norm_num [threeProb], ?_⟩
  rw [Fin.sum_univ_three]
  norm_num [threeProb]

/-- **The three category instance**: under `Multinomial(6; 1/2, 1/3, 1/6)` the first count is
`Bin(6, 1/2)`, the second has mean `2`, the first two have covariance `-1` and the third has
variance `5/6`. -/
theorem multinomialLaw_threeProb :
    (multinomialLaw 6 threeProb).map (fun n => n 0) = Bin(6, half) ∧
      ∫ n, (n 1 : ℝ) ∂multinomialLaw 6 threeProb = 2 ∧
      cov[fun n : Fin 3 → ℕ => (n 0 : ℝ), fun n => (n 1 : ℝ); multinomialLaw 6 threeProb] = -1 ∧
      Var[fun n : Fin 3 → ℕ => (n 2 : ℝ); multinomialLaw 6 threeProb] = 5 / 6 := by
  refine ⟨map_multinomialLaw_eval isWeights_threeProb 0 half (by simp [half, threeProb]), ?_, ?_,
    ?_⟩
  · rw [integral_multinomialLaw isWeights_threeProb]; norm_num [threeProb]
  · rw [covariance_multinomialLaw isWeights_threeProb]; norm_num [threeProb]
  · rw [variance_multinomialLaw isWeights_threeProb]; norm_num [threeProb]

/-! ### The binomial density -/

/-- **The binomial density instance**: `log P_{Bin(2,1/2)}(1) = log 2 + ℓ(2, 1, 1/2) = -log 2`. -/
theorem log_binomialDensity_half :
    Real.log (binomialDensity 2 (1 / 2) 1) = Real.log 2 + binomialLogLik 2 1 (1 / 2) ∧
      Real.log (binomialDensity 2 (1 / 2) 1) = -Real.log 2 := by
  have h := log_binomialDensity (n := 2) (y := 1) (by norm_num) (θ := 1 / 2) (by norm_num)
    (by norm_num)
  simp only [Nat.cast_one, Nat.cast_ofNat] at h
  refine ⟨by simpa using h, ?_⟩
  rw [h, binomialLogLik]
  norm_num
  rw [one_div, Real.log_inv]
  ring

end AggregateCountInstance

end NetworkMetaRegression

end CausalInference
