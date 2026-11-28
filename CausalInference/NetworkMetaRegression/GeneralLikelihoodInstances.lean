/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.NetworkMetaRegression.GeneralLikelihoodExamples
public import CausalInference.NetworkMetaRegression.AggregateCountPoisson
public import CausalInference.NetworkMetaRegression.AggregateCountMultinomial
public import CausalInference.NetworkMetaRegression.BridgeExamples

/-!
# Instances of the general likelihoods and their relation to the count laws

**Instances.**

* `map_pi_compProd_summary_apply_both`: with the covariate equally likely `0` or `1` and the
  logistic event probability `σ(x)`, both of two patients have the event with probability
  `θ²`, `θ = (1/2 + σ(1)) / 2`, read off the summary formula `map_pi_compProd_summary_apply`.
* `reductionModel_marginalLikelihood`: on a network of two studies without covariate effects,
  the general likelihood of the aggregate data `y = 1` on one arm and `y = 0` on another is
  `1/8` under any covariate law, and equals the arm based network likelihood.
* `poissonWitnessModel_card_singleton`: in a model with the prognostic effect `log 3` and the
  logistic link, one event among two patients with covariates equally likely `0` or `1` has
  probability `15/32`, the aggregate factor of `MultilevelModel.likelihood`.

**Relations to the count laws.**

* `binomialMass_eq_binomialDensity`: the two binomial masses agree at natural counts.
* `map_eventKernel_eq_bernoulliKernel`: `eventKernel q`, read through `true ↦ 1`, `false ↦ 0`,
  is `bernoulliKernel q`.
* `map_card_pi_compProd_eventKernel`: the number of events under `eventKernel q` has the law
  `Bin(n, ∫ q dF)`, the law of the count `∑ Yᵢ` under `bernoulliKernel q`
  (`map_card_eventKernel_eq_map_sum_bernoulliKernel`).
* `poissonDens_eq_poissonKernel`: `poissonDens` is the mass of `poissonKernel`.
* `stratumLaw_eq_count_withDensity`, `snd_compProd_categoricalKernel_eq`: the categorical law of
  `snd_compProd_categorical` is `stratumLaw` of the integrated probabilities.

## Main results

* `map_pi_compProd_summary_apply_both`, `reductionModel_marginalLikelihood`,
  `poissonWitnessModel_card_singleton`, `binomialMass_eq_binomialDensity`,
  `eventKernel_apply_eq_bernoulliMeasure`, `map_eventKernel_eq_bernoulliKernel`,
  `map_card_pi_compProd_eventKernel`, `map_card_eventKernel_eq_map_sum_bernoulliKernel`,
  `poissonDens_eq_poissonMeasure`, `poissonDens_eq_poissonKernel`,
  `stratumLaw_eq_count_withDensity`, `snd_compProd_categoricalKernel_eq`.

## References

* D. M. Phillippo, S. Dias, A. E. Ades, M. Belger, A. Brnabic, A. Schacht, D. Saure, Z. Kadziola
  and N. J. Welton, *Multilevel network meta-regression for population-adjusted treatment
  comparisons*, Journal of the Royal Statistical Society Series A 183 (2020).
-/

@[expose] public section

namespace CausalInference

namespace NetworkMetaRegression

open MeasureTheory ProbabilityTheory EffectMeasure
open scoped ENNReal NNReal unitInterval

/-! ### The binomial masses and kernels -/

/-- The binomial mass of `GeneralLikelihoodAggregate` is `binomialDensity` at a natural count.
This holds by unfolding. -/
theorem binomialMass_eq_binomialDensity (n : ℕ) (θ : ℝ) (s : ℕ) :
    binomialMass n θ s = binomialDensity n θ s := by
  rw [binomialMass, binomialDensity, Nat.floor_natCast]

/-- The binary outcome kernel at `x` is the Bernoulli law on `{true, false}` with parameter
`q(x) ∈ [0, 1]`. -/
theorem eventKernel_apply_eq_bernoulliMeasure {𝒳 : Type*} [MeasurableSpace 𝒳] {q : 𝒳 → ℝ}
    (hq : Measurable q) (h01 : ∀ x, q x ∈ I) (x : 𝒳) :
    eventKernel q x = Ber(true, false, ⟨q x, h01 x⟩) := by
  rw [eventKernel_apply hq, Measure.ext_iff_singleton]
  intro b
  rw [withDensity_apply _ (measurableSet_singleton b), Measure.restrict_singleton,
    Measure.count_singleton, one_smul, lintegral_dirac, bernoulliMeasure_def]
  cases b
  · simp only [Bool.false_eq_true, ↓reduceIte, FunLike.coe_add, FunLike.coe_smul,
      Pi.add_apply, Pi.smul_apply, Measure.dirac_apply_of_mem (Set.mem_singleton false)]
    rw [Measure.dirac_apply' _ (measurableSet_singleton false)]
    simp only [Set.indicator, Set.mem_singleton_iff, Bool.true_eq_false, ↓reduceIte, smul_zero,
      zero_add, ENNReal.smul_def, smul_eq_mul, mul_one]
    rw [ENNReal.ofReal_eq_coe_nnreal (sub_nonneg.mpr (h01 x).2)]
    rfl
  · simp only [↓reduceIte, FunLike.coe_add, FunLike.coe_smul, Pi.add_apply, Pi.smul_apply,
      Measure.dirac_apply_of_mem (Set.mem_singleton true)]
    rw [Measure.dirac_apply' _ (measurableSet_singleton true)]
    simp only [Set.indicator, Set.mem_singleton_iff, Bool.false_eq_true, ↓reduceIte, smul_zero,
      add_zero, ENNReal.smul_def, smul_eq_mul, mul_one]
    rw [ENNReal.ofReal_eq_coe_nnreal (h01 x).1]
    rfl

/-- **The binary outcome kernel and the Bernoulli kernel.** Read through `true ↦ 1` and
`false ↦ 0`, the binary outcome kernel with event probability `q(x) ∈ [0, 1]` is
`bernoulliKernel q`. -/
theorem map_eventKernel_eq_bernoulliKernel {𝒳 : Type*} [MeasurableSpace 𝒳] {q : 𝒳 → ℝ}
    (hq : Measurable q) (h01 : ∀ x, q x ∈ I) (x : 𝒳) :
    (eventKernel q x).map (fun b : Bool => if b then (1 : ℕ) else 0) =
      bernoulliKernel q hq h01 x := by
  rw [eventKernel_apply_eq_bernoulliMeasure hq h01, map_bernoulliMeasure, bernoulliKernel_apply]
  rfl

/-- **The number of events is binomial.** If the event probability `q(x) ∈ [0, 1]` is
measurable and the pairs of `n` patients are independent with law `F ⊗ eventKernel q`, the
number of events has the law `Bin(n, ∫ q dF)`. -/
theorem map_card_pi_compProd_eventKernel {𝒳 : Type*} [MeasurableSpace 𝒳] (F : Measure 𝒳)
    [IsProbabilityMeasure F] {q : 𝒳 → ℝ} (hq : Measurable q) (h01 : ∀ x, q x ∈ I) (n : ℕ) :
    haveI := isMarkovKernel_eventKernel hq (fun x => (h01 x).1) (fun x => (h01 x).2)
    (Measure.pi fun _ : Fin n => F ⊗ₘ eventKernel q).map
        (fun z => (Finset.univ.filter fun i => (z i).2 = true).card) =
      Bin(n, ⟨∫ x, q x ∂F, integral_mem_unitInterval hq h01⟩) := by
  have := isMarkovKernel_eventKernel hq (fun x => (h01 x).1) (fun x => (h01 x).2)
  rw [Measure.ext_iff_singleton]
  intro s
  rw [map_pi_compProd_card_singleton F hq _
    (Filter.Eventually.of_forall (eventKernel_apply hq)) s, binomial_singleton, binomialMass]

/-- **The two forms of the binomial count agree.** The number of events of `n` patients under
`F ⊗ eventKernel q` and the count `∑ Yᵢ` under `F ⊗ bernoulliKernel q` have the same law. -/
theorem map_card_eventKernel_eq_map_sum_bernoulliKernel {𝒳 : Type*} [MeasurableSpace 𝒳]
    (F : Measure 𝒳) [IsProbabilityMeasure F] {q : 𝒳 → ℝ} (hq : Measurable q)
    (h01 : ∀ x, q x ∈ I) (n : ℕ) :
    haveI := isMarkovKernel_eventKernel hq (fun x => (h01 x).1) (fun x => (h01 x).2)
    (Measure.pi fun _ : Fin n => F ⊗ₘ eventKernel q).map
        (fun z => (Finset.univ.filter fun i => (z i).2 = true).card) =
      (Measure.pi fun _ : Fin n => F ⊗ₘ bernoulliKernel q hq h01).map
        (fun z => ∑ i, (z i).2) := by
  rw [map_card_pi_compProd_eventKernel F hq h01 n,
    (map_sum_pi_compProd_bernoulli F hq h01 n).2]

/-! ### The Poisson mass -/

/-- `poissonDens θ k` is the mass of the Poisson law with rate `θ ≥ 0` at `k`. -/
theorem poissonDens_eq_poissonMeasure {θ : ℝ} (hθ : 0 ≤ θ) (k : ℕ) :
    poissonDens θ k = (poissonMeasure θ.toNNReal).real {k} := by
  rw [poissonMeasure_real_singleton, Real.coe_toNNReal θ hθ, poissonDens, Nat.floor_natCast]
  ring

/-- `poissonDens (r x) k` is the mass at `k` of the Poisson outcome kernel with nonnegative rate
`r`. -/
theorem poissonDens_eq_poissonKernel {𝒳 : Type*} [MeasurableSpace 𝒳] {r : 𝒳 → ℝ}
    (hr : Measurable r) (h0 : ∀ x, 0 ≤ r x) (x : 𝒳) (k : ℕ) :
    poissonDens (r x) k = (poissonKernel r hr x).real {k} := by
  rw [poissonKernel_apply, poissonDens_eq_poissonMeasure (h0 x)]

/-! ### The categorical law -/

/-- The law of a finite stratifier with nonnegative level probabilities `p` is the counting
measure with density `p`. -/
theorem stratumLaw_eq_count_withDensity {K : Type*} [Fintype K] [MeasurableSpace K]
    [MeasurableSingletonClass K] (p : K → ℝ) :
    stratumLaw p = Measure.count.withDensity fun k => ENNReal.ofReal (p k) := by
  rw [Measure.ext_iff_singleton]
  intro k
  rw [stratumLaw_singleton, withDensity_apply _ (measurableSet_singleton k),
    Measure.restrict_singleton, Measure.count_singleton, one_smul, lintegral_dirac]

/-- **The integrated categorical law through `snd_compProd_categorical`.** For measurable
category probabilities `π_k(x)` that are weights for every `x`, the category of a patient drawn
from `F` under `categoricalKernel π` has the law `stratumLaw θ`, `θ_k = ∫ π_k dF`. This is
`snd_compProd_categoricalKernel`, derived from `snd_compProd_categorical` and
`stratumLaw_eq_count_withDensity`. -/
theorem snd_compProd_categoricalKernel_eq {𝒳 K : Type*} [MeasurableSpace 𝒳] [Fintype K]
    [MeasurableSpace K] [MeasurableSingletonClass K] (F : Measure 𝒳) [IsProbabilityMeasure F]
    {π : K → 𝒳 → ℝ} (hπ : ∀ k, Measurable (π k)) (hw : ∀ x, IsWeights fun k => π k x) :
    (F ⊗ₘ categoricalKernel π hπ hw).snd = stratumLaw fun k => ∫ x, π k x ∂F := by
  rw [stratumLaw_eq_count_withDensity]
  exact snd_compProd_categorical F (π := fun x k => π k x) hπ (fun x k => (hw x).1 k) _
    (Filter.Eventually.of_forall fun x => by
      rw [categoricalKernel_apply, stratumLaw_eq_count_withDensity])

/-! ### Instances -/

/-- **Both of two patients have the event.** With the covariate equally likely `0` or `1` and
the logistic event probability `σ(x)`, the summary `Y₁ ∧ Y₂` of two independent patients equals
`true` with probability `θ²`, `θ = (1/2 + σ(1)) / 2`, computed from the summary formula
`map_pi_compProd_summary_apply`. -/
theorem map_pi_compProd_summary_apply_both :
    haveI := isMarkovKernel_eventKernel measurable_sigmoid_zero
      (fun x => Real.sigmoid_nonneg (x 0)) (fun x => Real.sigmoid_le_one (x 0))
    (Measure.pi fun _ : Fin 2 => halfLaw ⊗ₘ eventKernel fun x => Real.sigmoid (x 0)).map
        (fun z => (z 0).2 && (z 1).2) {true} =
      ENNReal.ofReal (((1 / 2 + Real.sigmoid 1) / 2) ^ 2) := by
  have := isMarkovKernel_eventKernel measurable_sigmoid_zero
    (fun x => Real.sigmoid_nonneg (x 0)) (fun x => Real.sigmoid_le_one (x 0))
  set L : (Fin 1 → ℝ) → Bool → ℝ≥0∞ := fun x b =>
    ENNReal.ofReal (if b then Real.sigmoid (x 0) else 1 - Real.sigmoid (x 0)) with hL
  have hLm : Measurable (Function.uncurry L) := by
    refine measurable_from_prod_countable_left fun b => ?_
    cases b
    · exact (measurable_const.sub measurable_sigmoid_zero).ennreal_ofReal
    · exact measurable_sigmoid_zero.ennreal_ofReal
  have hT : Measurable fun y : Fin 2 → Bool => y 0 && y 1 := measurable_of_countable _
  have h := map_pi_compProd_summary_apply (fun _ : Fin 2 => halfLaw) Measure.count
    (fun _ => eventKernel fun x => Real.sigmoid (x 0)) (fun _ => L) (fun _ => hLm)
    (fun _ => Filter.Eventually.of_forall (eventKernel_apply measurable_sigmoid_zero))
    hT (measurableSet_singleton true)
  have hpre : (fun y : Fin 2 → Bool => y 0 && y 1) ⁻¹' {true} = {fun _ => true} := by
    ext y
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Bool.and_eq_true, funext_iff,
      Fin.forall_fin_two]
  have hone : (Measure.pi fun _ : Fin 2 => (Measure.count : Measure Bool))
      {fun _ => true} = 1 := by
    rw [← Set.univ_pi_singleton, Measure.pi_pi]
    simp
  have hθ : ∫⁻ x, L x true ∂halfLaw = ENNReal.ofReal ((1 / 2 + Real.sigmoid 1) / 2) := by
    simp only [hL, ↓reduceIte]
    rw [← ofReal_integral_eq_lintegral_ofReal _
      (Filter.Eventually.of_forall fun x => Real.sigmoid_nonneg _), integral_sigmoid_halfLaw]
    exact Integrable.of_bound measurable_sigmoid_zero.aestronglyMeasurable 1
      (Filter.Eventually.of_forall fun x => by
        rw [Real.norm_eq_abs, abs_of_nonneg (Real.sigmoid_nonneg _)]
        exact Real.sigmoid_le_one _)
  rw [h, hpre, lintegral_singleton, hone, mul_one, Fin.prod_univ_two, hθ,
    ← ENNReal.ofReal_mul (by linarith [Real.sigmoid_nonneg 1]), sq]

/-- **The general likelihood on a network without covariate effects.** For the model
`reductionModel` (no prognostic or interaction effects), the Bernoulli density, any covariate
laws `F` and the aggregate data `y = 1` on the arm `A` of the first study and `y = 0` on the
arm `B` of the second, the general likelihood is `1/2 · (1 - 3/4) = 1/8`, and it equals the arm
based network likelihood at `nmaCoef`. -/
theorem reductionModel_marginalLikelihood (F : Fin 2 → Measure (Fin 1 → ℝ))
    [∀ j, IsProbabilityMeasure (F j)] :
    reductionModel.marginalLikelihood bernoulliDensity F [] [(armA, 1), (armB, 0)] =
        ENNReal.ofReal (1 / 8) ∧
      reductionModel.marginalLikelihood bernoulliDensity F [] [(armA, 1), (armB, 0)] =
        armLikelihood bernoulliDensity bernoulliDensity id (fun _ => 2) 2
          (reductionModel.nmaCoef (fun _ => 2) 2) [] [(armA, 1), (armB, 0)] := by
  have h := MultilevelModel.marginalLikelihood_eq_armLikelihood bernoulliDensity reductionModel
    rfl (fun _ => rfl) F (fun _ => 2) 2 [] [(armA, 1), (armB, 0)]
  rw [List.map_nil] at h
  exact ⟨h.trans (reductionExample_likelihood bernoulliDensity).2, h⟩

/-- The logistic mean surface of `poissonWitnessModel`: `σ(x log 3)`. -/
theorem poissonWitnessModel_surface (x : Fin 1 → ℝ) :
    poissonWitnessModel.surface Real.sigmoid (poissonWitnessModel.μ ()) () x =
      Real.sigmoid (x 0 * Real.log 3) := by
  simp [MultilevelModel.surface, MultilevelModel.eta,
    NetworkMetaAnalysis.metaRegressionPredictor, poissonWitnessModel, dotProduct]

theorem measurable_poissonWitnessModel_surface :
    Measurable (poissonWitnessModel.surface Real.sigmoid (poissonWitnessModel.μ ()) ()) :=
  poissonWitnessModel.measurable_surface continuous_sigmoid.measurable _ _

/-- **One event among two patients in a model with a prognostic effect.** In
`poissonWitnessModel` (prognostic effect `log 3`) with the logistic link, covariates equally
likely `0` or `1` and the binary outcome kernel at the mean surface, one event among two
independent patients has probability `15/32`, the aggregate factor of
`MultilevelModel.likelihood` with the binomial summary density at the arm mean `5/8`. -/
theorem poissonWitnessModel_card_singleton (f : ℝ → ℝ → ℝ) :
    haveI := isMarkovKernel_eventKernel measurable_poissonWitnessModel_surface
      (fun _ => Real.sigmoid_nonneg _) (fun _ => Real.sigmoid_le_one _)
    (Measure.pi fun _ : Fin 2 => halfLaw ⊗ₘ
        eventKernel (poissonWitnessModel.surface Real.sigmoid (poissonWitnessModel.μ ()) ())).map
        (fun z => (Finset.univ.filter fun i => (z i).2 = true).card) {1} =
      poissonWitnessModel.likelihood f (fun θ y => binomialMass 2 θ ⌊y⌋₊) Real.sigmoid
        (fun _ => halfLaw) [] [(poissonWitnessArm, ((1 : ℕ) : ℝ))] ∧
    poissonWitnessModel.likelihood f (fun θ y => binomialMass 2 θ ⌊y⌋₊) Real.sigmoid
        (fun _ => halfLaw) [] [(poissonWitnessArm, ((1 : ℕ) : ℝ))] = ENNReal.ofReal (15 / 32) := by
  have := isMarkovKernel_eventKernel measurable_poissonWitnessModel_surface
    (fun _ => Real.sigmoid_nonneg _) (fun _ => Real.sigmoid_le_one _)
  refine ⟨MultilevelModel.map_card_singleton_eq_likelihood f continuous_sigmoid.measurable
    poissonWitnessModel (fun _ => halfLaw) poissonWitnessArm _
    (eventKernel_apply measurable_poissonWitnessModel_surface) 2 1, ?_⟩
  have h3 : Real.sigmoid (Real.log 3) = 3 / 4 := by
    rw [Real.sigmoid_def, Real.exp_neg, Real.exp_log (by norm_num)]
    norm_num
  have hmean : poissonWitnessModel.armMean Real.sigmoid (poissonWitnessModel.μ ()) halfLaw () =
      5 / 8 := by
    rw [MultilevelModel.armMean, halfLaw, integral_twoAtomLaw (by norm_num) (by norm_num),
      poissonWitnessModel_surface, poissonWitnessModel_surface]
    simp only [zero_mul, one_mul, Real.sigmoid_zero, h3]
    norm_num
  simp only [MultilevelModel.likelihood, List.map_nil, List.prod_nil, one_mul, List.map_cons,
    List.prod_cons, mul_one]
  change ENNReal.ofReal (binomialMass 2
    (poissonWitnessModel.armMean Real.sigmoid (poissonWitnessModel.μ ()) halfLaw ()) _) = _
  rw [hmean, Nat.cast_one, Nat.floor_one, binomialMass]
  norm_num

end NetworkMetaRegression

end CausalInference
