/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.NetworkMetaRegression.GeneratingFunction
public import CausalInference.NetworkMetaRegression.ReductionLikelihood
public import CausalInference.NetworkMetaAnalysis.Deviance
public import Mathlib.Probability.Distributions.Binomial
public import Mathlib.Probability.Distributions.Bernoulli
public import Mathlib.Probability.Moments.Variance
public import Mathlib.Algebra.Polynomial.BigOperators
public import Mathlib.Algebra.Polynomial.Eval.Degree

/-!
# The aggregate count of a binary outcome

An arm of `n` patients reports the number of events `∑ Yᵢ`. In the multilevel model of
Phillippo et al. (2020) a patient with covariates `x` has an event with probability `m(x)`, the
mean surface `g⁻¹(η(x))`.

* **Given the covariates the count is Poisson binomial** (`map_sum_eq_poissonBinomial`,
  `measureReal_poissonBinomial_singleton`, `generatingFunction_poissonBinomial`,
  `integral_variance_poissonBinomial`): for fixed covariates `x₁, …, xₙ` the count of
  independent `Ber(m(xᵢ))` outcomes has the Poisson binomial law with risks `m(xᵢ)`, with mass
  function the coefficients of `∏ (1 - qᵢ + qᵢ z)`, generating function that product for every
  real `z`, mean `∑ qᵢ` and variance `∑ qᵢ (1 - qᵢ)`.
* **With covariates integrated out the count is binomial** (`map_sum_pi_compProd_bernoulli`):
  if the covariates are independent draws from a law `F`, the count of the arm is exactly
  `Bin(n, θ)` with `θ = ∫ m dF`. For the multilevel model `θ` is the aggregate arm mean
  (`MultilevelModel.map_sum_pi_compProd_eq_binomial`), and the aggregate factor of the
  likelihood with the binomial summary density is the probability of the observed count
  (`MultilevelModel.likelihood_cons_binomialDensity`).
* **The two laws differ** (`poissonBinomial_eq_binomial_iff`): the Poisson binomial law with
  risks `q` is `Bin(n, θ)` exactly when every `qᵢ = θ`; the conditional law is never binomial
  when the risks differ.
* **The binomial law** (`poissonBinomial_const`, `variance_binomial`): `Bin(n, θ)` is the equal
  risk Poisson binomial, with variance `n θ (1 - θ)`.

## Main definitions

* `bernoulliKernel`, `poissonBinomial`, `poissonBinomialPoly`, `binomialDensity`.

## Main results

* `map_sum_eq_poissonBinomial`, `measureReal_poissonBinomial_singleton`,
  `generatingFunction_poissonBinomial`, `integral_variance_poissonBinomial`.
* `poissonBinomial_const`, `variance_binomial`, `poissonBinomial_eq_binomial_iff`.
* `snd_compProd_bernoulliKernel`, `map_sum_pi_compProd_bernoulli`.
* `MultilevelModel.map_sum_pi_compProd_eq_binomial`,
  `MultilevelModel.likelihood_cons_binomialDensity`, `log_binomialDensity`.

## References

* D. M. Phillippo, S. Dias, A. E. Ades, M. Belger, A. Brnabic, A. Schacht, D. Saure, Z. Kadziola
  and N. J. Welton, *Multilevel network meta-regression for population-adjusted treatment
  comparisons*, Journal of the Royal Statistical Society Series A 183 (2020).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Polynomial
open scoped NNReal ENNReal unitInterval

namespace CausalInference

namespace NetworkMetaRegression

/-! ### The Bernoulli kernel -/

section Kernel

variable {𝒳 : Type*} [MeasurableSpace 𝒳]

/-- The **Bernoulli outcome kernel** of a mean function `m` with values in `[0, 1]`: a patient
with covariates `x` has the outcome law `Ber(m(x))` on `{0, 1} ⊆ ℕ`. -/
noncomputable def bernoulliKernel (m : 𝒳 → ℝ) (hm : Measurable m) (h01 : ∀ x, m x ∈ I) :
    Kernel 𝒳 ℕ where
  toFun x := Ber(1, 0, ⟨m x, h01 x⟩)
  measurable' := by
    refine Measure.measurable_of_measurable_coe _ fun s _ => ?_
    simp only [bernoulliMeasure_def, FunLike.coe_add, FunLike.coe_smul, Pi.add_apply,
      Pi.smul_apply, ENNReal.smul_def, smul_eq_mul]
    have h1 : Measurable fun x => (unitInterval.toNNReal ⟨m x, h01 x⟩ : ℝ≥0∞) :=
      (measurable_coe_nnreal_ennreal.comp unitInterval.toNNReal_continuous.measurable).comp
        (hm.subtype_mk)
    have h2 : Measurable fun x => (unitInterval.toNNReal (σ ⟨m x, h01 x⟩) : ℝ≥0∞) :=
      (measurable_coe_nnreal_ennreal.comp
        (unitInterval.toNNReal_continuous.comp unitInterval.continuous_symm).measurable).comp
        (hm.subtype_mk)
    exact (h1.mul_const _).add (h2.mul_const _)

theorem bernoulliKernel_apply (m : 𝒳 → ℝ) (hm : Measurable m) (h01 : ∀ x, m x ∈ I) (x : 𝒳) :
    bernoulliKernel m hm h01 x = Ber(1, 0, ⟨m x, h01 x⟩) :=
  rfl

instance (m : 𝒳 → ℝ) (hm : Measurable m) (h01 : ∀ x, m x ∈ I) :
    IsMarkovKernel (bernoulliKernel m hm h01) :=
  ⟨fun x => by rw [bernoulliKernel_apply]; infer_instance⟩

end Kernel

/-! ### Sums of independent counts -/

section Convolution

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- **The convolution formula for independent counts**:
`P(X + Y = k) = ∑_{i + j = k} P(X = i) P(Y = j)`. -/
theorem measure_sum_eq_antidiagonal_of_indepFun {X Y : Ω → ℕ} (hX : Measurable X)
    (hY : Measurable Y) (hXY : IndepFun X Y μ) (k : ℕ) :
    μ {ω | X ω + Y ω = k} =
      ∑ ij ∈ Finset.antidiagonal k, μ {ω | X ω = ij.1} * μ {ω | Y ω = ij.2} := by
  have hset : {ω | X ω + Y ω = k} =
      ⋃ ij ∈ Finset.antidiagonal k, ({ω | X ω = ij.1} ∩ {ω | Y ω = ij.2}) := by
    ext ω; simp
  rw [hset, measure_biUnion_finset]
  · refine Finset.sum_congr rfl fun ij _ => ?_
    exact hXY.measure_inter_preimage_eq_mul {ij.1} {ij.2} (measurableSet_singleton _)
      (measurableSet_singleton _)
  · intro a _ b _ hab
    refine Set.disjoint_left.mpr fun ω h1 h2 => hab ?_
    simp only [Set.mem_inter_iff, Set.mem_ofPred_eq] at h1 h2
    exact Prod.ext (h1.1.symm.trans h2.1) (h1.2.symm.trans h2.2)
  · exact fun ij _ => (hX (measurableSet_singleton _)).inter (hY (measurableSet_singleton _))

end Convolution

/-! ### The Poisson binomial law -/

section PoissonBinomial

/-- The generating polynomial `q z + (1 - q)` of `Ber(q)`. -/
noncomputable def bernoulliGenPoly (q : ℝ) : ℝ[X] := C q * X + C (1 - q)

/-- The generating polynomial `∏ (qᵢ z + 1 - qᵢ)` of the Poisson binomial law. -/
noncomputable def poissonBinomialPoly {n : ℕ} (q : Fin n → I) : ℝ[X] :=
  ∏ i, bernoulliGenPoly (q i)

/-- The **Poisson binomial law** with risks `q`: the law of the sum of independent `Ber(qᵢ)`
counts. -/
noncomputable def poissonBinomial {n : ℕ} (q : Fin n → I) : Measure ℕ :=
  (Measure.pi fun i => (Ber(1, 0, q i) : Measure ℕ)).map fun y => ∑ i, y i

theorem coeff_bernoulliGenPoly (q : ℝ) (k : ℕ) :
    (bernoulliGenPoly q).coeff k = if k = 0 then 1 - q else if k = 1 then q else 0 := by
  rcases k with _ | _ | k <;>
    simp only [bernoulliGenPoly, coeff_add, coeff_C_mul, coeff_X, coeff_C] <;> simp

theorem bernoulli_real_singleton (q : I) (k : ℕ) :
    (Ber(1, 0, q) : Measure ℕ).real {k} = (bernoulliGenPoly q).coeff k := by
  rw [coeff_bernoulliGenPoly]
  rcases k with _ | _ | k
  · simp [bernoulliMeasure_def, measureReal_def]
  · simp [bernoulliMeasure_def, measureReal_def]
  · simp [bernoulliMeasure_def, measureReal_def, Set.indicator]

theorem natDegree_poissonBinomialPoly_le {n : ℕ} (q : Fin n → I) :
    (poissonBinomialPoly q).natDegree ≤ n := by
  unfold poissonBinomialPoly
  refine (natDegree_prod_le _ _).trans ?_
  calc ∑ i, (bernoulliGenPoly (q i)).natDegree ≤ ∑ _i : Fin n, 1 :=
        Finset.sum_le_sum fun i _ => by
          unfold bernoulliGenPoly
          exact (natDegree_add_le _ _).trans (max_le ((natDegree_C_mul_le _ _).trans (by simp))
            (by simp))
    _ = n := by simp

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ] {n : ℕ}

/-- The law of a sum of independent Bernoulli counts over `s` puts on `k` the coefficient of
`z ^ k` in `∏_{i ∈ s} (qᵢ z + 1 - qᵢ)`. -/
theorem measureReal_finsetSum_eq_coeff_prod {Y : Fin n → Ω → ℕ} (hmeas : ∀ i, Measurable (Y i))
    (hind : iIndepFun Y μ) {q : Fin n → I} (hY : ∀ i, HasLaw (Y i) Ber(1, 0, q i) μ)
    (s : Finset (Fin n)) (k : ℕ) :
    μ.real {ω | ∑ i ∈ s, Y i ω = k} = (∏ i ∈ s, bernoulliGenPoly (q i)).coeff k := by
  classical
  induction s using Finset.induction_on generalizing k with
  | empty =>
    rcases eq_or_ne k 0 with rfl | hk
    · simp
    · simp [Ne.symm hk, coeff_one, hk]
  | insert a s ha ih =>
    have hYa : ∀ j, μ.real {ω | Y a ω = j} = (bernoulliGenPoly (q a)).coeff j := fun j => by
      rw [← bernoulli_real_singleton, ← (hY a).map_eq, map_measureReal_apply (hmeas a)
        (measurableSet_singleton j)]
      rfl
    have hS : Measurable fun ω => ∑ i ∈ s, Y i ω := Finset.measurable_sum _ fun i _ => hmeas i
    have hind' : IndepFun (fun ω => ∑ i ∈ s, Y i ω) (Y a) μ := by
      have := hind.indepFun_finsetSum_of_notMem hmeas ha
      convert this using 1
      funext ω; simp
    simp only [Finset.sum_insert ha, Finset.prod_insert ha]
    have h := measure_sum_eq_antidiagonal_of_indepFun (μ := μ) hS (hmeas a) hind' k
    simp only [add_comm (Y a _)]
    rw [measureReal_def, h, ENNReal.toReal_sum (fun _ _ => ENNReal.mul_ne_top
      (measure_ne_top _ _) (measure_ne_top _ _)), mul_comm, coeff_mul]
    refine Finset.sum_congr rfl fun ij _ => ?_
    rw [ENNReal.toReal_mul, ← measureReal_def, ← measureReal_def, ih, hYa]

/-- **Independent Bernoulli counts sum to a Poisson binomial count**: if `Yᵢ ∼ Ber(qᵢ)` are
independent, `∑ Yᵢ` has the Poisson binomial law with risks `q`. -/
theorem map_sum_eq_poissonBinomial {Y : Fin n → Ω → ℕ} (hmeas : ∀ i, Measurable (Y i))
    (hind : iIndepFun Y μ) {q : Fin n → I} (hY : ∀ i, HasLaw (Y i) Ber(1, 0, q i) μ) :
    μ.map (fun ω => ∑ i, Y i ω) = poissonBinomial q := by
  have h := (iIndepFun_iff_map_fun_eq_pi_map fun i => (hmeas i).aemeasurable).mp hind
  simp only [fun i => (hY i).map_eq] at h
  rw [poissonBinomial, ← h, Measure.map_map (by fun_prop) (by fun_prop)]
  rfl

theorem coords_pi_bernoulli (q : Fin n → I) :
    iIndepFun (fun i (y : Fin n → ℕ) => y i) (Measure.pi fun i => (Ber(1, 0, q i) : Measure ℕ)) ∧
      ∀ i, HasLaw (fun y : Fin n → ℕ => y i) Ber(1, 0, q i)
        (Measure.pi fun i => (Ber(1, 0, q i) : Measure ℕ)) := by
  classical
  refine ⟨iIndepFun_pi (X := fun _ (k : ℕ) => k) fun _ => aemeasurable_id, fun i =>
    ⟨(measurable_pi_apply i).aemeasurable, ?_⟩⟩
  rw [show (fun y : Fin n → ℕ => y i) = Function.eval i from rfl, Measure.pi_map_eval]
  simp

instance (q : Fin n → I) : IsProbabilityMeasure (poissonBinomial q) := by
  unfold poissonBinomial
  exact (Measure.isProbabilityMeasure_map_iff (Finset.measurable_sum
    (f := fun i (y : Fin n → ℕ) => y i) _ fun i _ => measurable_pi_apply i).aemeasurable).mpr
    inferInstance

/-- **The mass function of the Poisson binomial law**: the law with risks `q` puts on `k` the
coefficient of `z ^ k` in `∏ (qᵢ z + 1 - qᵢ)`, which is the subset sum
`∑_{|A| = k} ∏_{i ∈ A} qᵢ ∏_{i ∉ A} (1 - qᵢ)`. -/
theorem measureReal_poissonBinomial_singleton (q : Fin n → I) (k : ℕ) :
    (poissonBinomial q).real {k} = (poissonBinomialPoly q).coeff k ∧
      (poissonBinomialPoly q).coeff k = ∑ A ∈ Finset.powersetCard k Finset.univ,
        (∏ i ∈ A, (q i : ℝ)) * ∏ i ∈ Finset.univ \ A, (1 - (q i : ℝ)) := by
  classical
  obtain ⟨hind, hY⟩ := coords_pi_bernoulli q
  refine ⟨?_, ?_⟩
  · rw [poissonBinomialPoly,
      ← measureReal_finsetSum_eq_coeff_prod (fun i => measurable_pi_apply i) hind hY Finset.univ k,
      poissonBinomial, map_measureReal_apply (by fun_prop) (measurableSet_singleton k)]
    rfl
  · simp only [poissonBinomialPoly, bernoulliGenPoly]
    rw [Finset.prod_add, finsetSum_coeff, Finset.powersetCard_eq_filter, Finset.sum_filter]
    refine Finset.sum_congr rfl fun A _ => ?_
    rw [Finset.prod_mul_distrib, Finset.prod_const, ← map_prod C, ← map_prod C, mul_comm (C _),
      mul_assoc, ← C_mul, coeff_X_pow_mul', coeff_C]
    by_cases hA : A.card = k
    · simp [hA]
    · simp [hA]
      omega

theorem coeff_poissonBinomialPoly_nonneg (q : Fin n → I) (k : ℕ) :
    0 ≤ (poissonBinomialPoly q).coeff k := by
  rw [← (measureReal_poissonBinomial_singleton q k).1]; exact measureReal_nonneg

/-- **The generating function of the Poisson binomial law**: `G(z) = ∏ (1 - qᵢ + qᵢ z)` for
every real `z` (the law has finite support, so every `z ^ k` is integrable). -/
theorem generatingFunction_poissonBinomial (q : Fin n → I) (z : ℝ) :
    generatingFunction (poissonBinomial q) z = ∏ i, (1 - (q i : ℝ) + q i * z) := by
  obtain ⟨hind, hY⟩ := coords_pi_bernoulli q
  rw [poissonBinomial, generatingFunction_map (by fun_prop)]
  simp only [← Finset.prod_pow_eq_pow_sum]
  rw [hind.integral_fun_prod_comp (f := fun _ (k : ℕ) => z ^ k)
    (fun i => (measurable_pi_apply i).aemeasurable)
    (fun _ => Measurable.of_discrete.aestronglyMeasurable)]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [← integral_map (measurable_pi_apply i).aemeasurable
    Measurable.of_discrete.aestronglyMeasurable, (hY i).map_eq, integral_bernoulliMeasure]
  simp only [pow_one, pow_zero, smul_eq_mul, mul_one]
  ring

private lemma integral_bernoulli_comp (q : I) (g : ℕ → ℝ) :
    ∫ k, g k ∂(Ber(1, 0, q) : Measure ℕ) = q * g 1 + (1 - q) * g 0 := by
  rw [integral_bernoulliMeasure]; simp

/-- **The mean and variance of the Poisson binomial law**: `∑ qᵢ` and `∑ qᵢ (1 - qᵢ)`. -/
theorem integral_variance_poissonBinomial (q : Fin n → I) :
    ∫ k, (k : ℝ) ∂(poissonBinomial q) = ∑ i, (q i : ℝ) ∧
      variance (fun k : ℕ => (k : ℝ)) (poissonBinomial q) = ∑ i, (q i : ℝ) * (1 - q i) := by
  obtain ⟨hind, hY⟩ := coords_pi_bernoulli q
  set P := Measure.pi fun i => (Ber(1, 0, q i) : Measure ℕ)
  set Z : Fin n → (Fin n → ℕ) → ℝ := fun i y => (y i : ℝ) with hZ
  have hZm : ∀ i, Measurable (Z i) := fun i => measurable_from_nat.comp (measurable_pi_apply i)
  have hlaw : ∀ i (g : ℕ → ℝ), ∫ y, g (y i) ∂P = q i * g 1 + (1 - q i) * g 0 := fun i g => by
    rw [← integral_map (measurable_pi_apply i).aemeasurable (by fun_prop), (hY i).map_eq,
      integral_bernoulli_comp]
  have hmem : ∀ i, MemLp (Z i) 2 P := fun i => by
    rw [memLp_two_iff_integrable_sq (hZm i).aestronglyMeasurable]
    have h : Integrable (fun k : ℕ => (k : ℝ) ^ 2) (P.map fun y => y i) := by
      rw [(hY i).map_eq]; exact integrable_bernoulliMeasure _ _ _ _
    exact h.comp_measurable (measurable_pi_apply i)
  have hsum : (fun y : Fin n → ℕ => ((∑ i, y i : ℕ) : ℝ)) = ∑ i, Z i := by
    funext y; simp [hZ]
  rw [poissonBinomial, integral_map (by fun_prop) (by fun_prop),
    variance_map (by fun_prop) (by fun_prop)]
  change ∫ y, ((∑ i, y i : ℕ) : ℝ) ∂P = _ ∧ variance (fun y => ((∑ i, y i : ℕ) : ℝ)) P = _
  refine ⟨?_, ?_⟩
  · rw [hsum, show (∫ y, (∑ i, Z i) y ∂P) = ∫ y, ∑ i, Z i y ∂P by simp,
      integral_finsetSum _ fun i _ => (hmem i).integrable one_le_two]
    exact Finset.sum_congr rfl fun i _ => by rw [hZ, hlaw i (fun k => (k : ℝ))]; simp
  · rw [hsum, IndepFun.variance_sum (fun i _ => hmem i) fun i _ j _ hij =>
      (hind.indepFun hij).comp measurable_from_nat measurable_from_nat]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [variance_eq_sub (hmem i)]
    have h1 : ∫ y, Z i y ∂P = q i := by rw [hZ, hlaw i (fun k => (k : ℝ))]; simp
    have h2 : ∫ y, (Z i ^ 2) y ∂P = q i := by
      simp only [Pi.pow_apply, hZ]
      rw [hlaw i (fun k => (k : ℝ) ^ 2)]; simp
    rw [h2, h1]; ring

/-- **The binomial law is the equal risk Poisson binomial law**: with all risks `θ` it is
`Bin(n, θ)`. -/
theorem poissonBinomial_const (θ : I) : poissonBinomial (fun _ : Fin n => θ) = Bin(n, θ) := by
  classical
  refine Measure.ext_of_singleton fun k => ?_
  rw [← ofReal_measureReal, (measureReal_poissonBinomial_singleton _ k).1, binomial_singleton,
    (measureReal_poissonBinomial_singleton _ k).2]
  congr 1
  rw [Finset.sum_congr rfl fun A hA => by
    rw [Finset.prod_const, Finset.prod_const, Finset.card_sdiff_of_subset (Finset.subset_univ _),
      (Finset.mem_powersetCard.mp hA).2, Finset.card_univ, Fintype.card_fin],
    Finset.sum_const, Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  ring

/-- **The variance of the binomial law**: `Var Bin(n, θ) = n θ (1 - θ)`. -/
theorem variance_binomial (θ : I) :
    variance (fun k : ℕ => (k : ℝ)) Bin(n, θ) = n * θ * (1 - θ) := by
  rw [← poissonBinomial_const, (integral_variance_poissonBinomial _).2]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  ring

theorem integral_binomial_id (θ : I) : ∫ k, (k : ℝ) ∂Bin(n, θ) = n * θ := by
  rw [← poissonBinomial_const, (integral_variance_poissonBinomial _).1]
  simp

/-- **The conditional law is binomial only for equal risks**: the Poisson binomial law with
risks `q` is `Bin(n, θ)` exactly when every `qᵢ = θ`. The mean gives `∑ qᵢ = n θ` and the
variance `∑ qᵢ² = n θ²`, so `∑ (qᵢ - θ)² = 0`. -/
theorem poissonBinomial_eq_binomial_iff (q : Fin n → I) (θ : I) :
    poissonBinomial q = Bin(n, θ) ↔ ∀ i, q i = θ := by
  refine ⟨fun h => ?_, fun h => by rw [funext h]; exact poissonBinomial_const θ⟩
  obtain ⟨h1, h2⟩ := integral_variance_poissonBinomial q
  rw [h, integral_binomial_id] at h1
  rw [h, variance_binomial] at h2
  have hsq : ∑ i, ((q i : ℝ) - θ) ^ 2 = 0 := by
    have e : ∑ i, ((q i : ℝ) - θ) ^ 2 =
        (∑ i, (q i : ℝ)) - ∑ i, (q i : ℝ) * (1 - q i) - 2 * θ * ∑ i, (q i : ℝ) + n * θ ^ 2 := by
      simp only [Finset.mul_sum, ← Finset.sum_sub_distrib]
      rw [show (n : ℝ) * (θ : ℝ) ^ 2 = ∑ _i : Fin n, (θ : ℝ) ^ 2 by simp]
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [e, ← h1, ← h2]; ring
  intro i
  have := (Finset.sum_eq_zero_iff_of_nonneg fun j _ => sq_nonneg ((q j : ℝ) - θ)).mp hsq i
    (Finset.mem_univ i)
  exact Subtype.ext (by nlinarith [sq_nonneg ((q i : ℝ) - θ)])

end PoissonBinomial

/-! ### The integrated binomial law -/

section Integrated

variable {𝒳 : Type*} [MeasurableSpace 𝒳]

theorem integral_mem_unitInterval {F : Measure 𝒳} [IsProbabilityMeasure F] {m : 𝒳 → ℝ}
    (hm : Measurable m) (h01 : ∀ x, m x ∈ I) : ∫ x, m x ∂F ∈ I := by
  have hmi : Integrable m F := (integrable_const 1).mono' hm.aestronglyMeasurable
    (ae_of_all _ fun x => by rw [Real.norm_eq_abs, abs_of_nonneg (h01 x).1]; exact (h01 x).2)
  exact ⟨integral_nonneg fun x => (h01 x).1, by
    calc ∫ x, m x ∂F ≤ ∫ _x, (1 : ℝ) ∂F := integral_mono hmi (integrable_const 1)
            fun x => (h01 x).2
      _ = 1 := by simp⟩

/-- **The outcome of a patient drawn from the covariate law is Bernoulli with the averaged
risk**: under the joint law `F ⊗ Ber(m(x))` the outcome has the law `Ber(θ)`,
`θ = ∫ m dF`. -/
theorem snd_compProd_bernoulliKernel (F : Measure 𝒳) [IsProbabilityMeasure F] {m : 𝒳 → ℝ}
    (hm : Measurable m) (h01 : ∀ x, m x ∈ I) :
    (F ⊗ₘ bernoulliKernel m hm h01).snd =
      Ber(1, 0, ⟨∫ x, m x ∂F, integral_mem_unitInterval hm h01⟩) := by
  have hmi : Integrable m F := (integrable_const 1).mono' hm.aestronglyMeasurable
    (ae_of_all _ fun x => by rw [Real.norm_eq_abs, abs_of_nonneg (h01 x).1]; exact (h01 x).2)
  rw [Measure.snd_compProd]
  refine Measure.ext_of_singleton fun k => ?_
  rw [Measure.bind_apply (measurableSet_singleton k) (Kernel.aemeasurable _)]
  simp_rw [bernoulliKernel_apply]
  have hs : ∀ (r : I), (Ber(1, 0, r) : Measure ℕ) {k} =
      ENNReal.ofReal ((bernoulliGenPoly r).coeff k) := fun r => by
    rw [← bernoulli_real_singleton, ofReal_measureReal]
  simp_rw [hs, coeff_bernoulliGenPoly]
  rcases k with _ | _ | k
  · simp only [ite_true]
    have hi : Integrable (fun x => 1 - m x) F := (integrable_const 1).sub hmi
    rw [← ofReal_integral_eq_lintegral_ofReal hi
      (ae_of_all _ fun x => sub_nonneg.mpr (h01 x).2), integral_sub (integrable_const 1) hmi]
    simp
  · simp only [zero_add, one_ne_zero, ite_false, ite_true]
    exact (ofReal_integral_eq_lintegral_ofReal hmi (ae_of_all _ fun x => (h01 x).1)).symm
  · simp

/-- **With covariates integrated out the count is binomial**: if the pairs `(Xᵢ, Yᵢ)` of `n`
patients are independent with covariates `Xᵢ ∼ F` and outcome `Yᵢ ∼ Ber(m(Xᵢ))` given `Xᵢ`,
the outcomes are independent `Ber(θ)` and the count `∑ Yᵢ` is exactly `Bin(n, θ)`, with
`θ = ∫ m dF`. -/
theorem map_sum_pi_compProd_bernoulli (F : Measure 𝒳) [IsProbabilityMeasure F] {m : 𝒳 → ℝ}
    (hm : Measurable m) (h01 : ∀ x, m x ∈ I) (n : ℕ) :
    (Measure.pi fun _ : Fin n => F ⊗ₘ bernoulliKernel m hm h01).map (fun z i => (z i).2) =
        Measure.pi (fun _ : Fin n =>
          (Ber(1, 0, ⟨∫ x, m x ∂F, integral_mem_unitInterval hm h01⟩) : Measure ℕ)) ∧
      (Measure.pi fun _ : Fin n => F ⊗ₘ bernoulliKernel m hm h01).map (fun z => ∑ i, (z i).2) =
        Bin(n, ⟨∫ x, m x ∂F, integral_mem_unitInterval hm h01⟩) := by
  have hsnd := snd_compProd_bernoulliKernel F hm h01
  have hpi : (Measure.pi fun _ : Fin n => F ⊗ₘ bernoulliKernel m hm h01).map
      (fun z i => (z i).2) = Measure.pi (fun _ : Fin n =>
        (Ber(1, 0, ⟨∫ x, m x ∂F, integral_mem_unitInterval hm h01⟩) : Measure ℕ)) := by
    rw [Measure.pi_map_pi (fun _ => measurable_snd.aemeasurable)]
    exact congrArg Measure.pi (funext fun _ => hsnd)
  refine ⟨hpi, ?_⟩
  rw [show (fun z : Fin n → 𝒳 × ℕ => ∑ i, (z i).2) =
      (fun y : Fin n → ℕ => ∑ i, y i) ∘ (fun z i => (z i).2) from rfl,
    ← Measure.map_map (by fun_prop) (by fun_prop), hpi, ← poissonBinomial_const]
  rfl

end Integrated

/-! ### The multilevel model -/

/-- The **binomial summary density** of an arm of `n` patients: the mass `C(n, y) θ ^ y
(1 - θ) ^ (n - y)` of `Bin(n, θ)` at the count `y` (a real summary is read as its natural
floor). -/
noncomputable def binomialDensity (n : ℕ) (θ y : ℝ) : ℝ :=
  n.choose ⌊y⌋₊ * θ ^ ⌊y⌋₊ * (1 - θ) ^ (n - ⌊y⌋₊)

/-- **The binomial log likelihood**: for `0 < θ < 1` and a count `y ≤ n`, the log of the binomial
density is `log C(n, y)` plus `binomialLogLik n y θ`. -/
theorem log_binomialDensity {n y : ℕ} (hy : y ≤ n) {θ : ℝ} (h0 : 0 < θ) (h1 : θ < 1) :
    Real.log (binomialDensity n θ y) =
      Real.log (n.choose y) + NetworkMetaAnalysis.binomialLogLik n y θ := by
  have hc : (0 : ℝ) < n.choose y := by exact_mod_cast Nat.choose_pos hy
  rw [binomialDensity, Nat.floor_natCast, Real.log_mul (by positivity) (by
      have : 0 < 1 - θ := by linarith
      positivity),
    Real.log_mul hc.ne' (by positivity), Real.log_pow, Real.log_pow,
    NetworkMetaAnalysis.binomialLogLik, Nat.cast_sub hy]
  ring

namespace MultilevelModel

open NetworkMetaAnalysis

variable {J K : Type*} {p : ℕ}

/-- An inverse link with values in `[0, 1]` gives a mean surface with values in `[0, 1]`. -/
theorem surface_mem_unitInterval {ginv : ℝ → ℝ} (h01 : ∀ y, ginv y ∈ I)
    (M : MultilevelModel J K p) (α : ℝ) (k : K) (x : Fin p → ℝ) : M.surface ginv α k x ∈ I :=
  h01 _

/-- **The aggregate count of the multilevel model for a binary outcome is binomial at the arm
mean**: if the inverse link takes values in `[0, 1]`, the covariates of the `n` patients of an
arm are independent draws from `F` and the outcome of a patient with covariates `x` is
`Ber(g⁻¹(η_k(x)))`, the count of events of the arm has the law `Bin(n, θ)` with
`θ = ∫ g⁻¹(η_k) dF` the aggregate arm mean. -/
theorem map_sum_pi_compProd_eq_binomial {ginv : ℝ → ℝ} (hginv : Measurable ginv)
    (h01 : ∀ y, ginv y ∈ I) (M : MultilevelModel J K p) (α : ℝ) (k : K)
    (F : Measure (Fin p → ℝ)) [IsProbabilityMeasure F] (n : ℕ) :
    (Measure.pi fun _ : Fin n =>
        F ⊗ₘ bernoulliKernel (M.surface ginv α k) (M.measurable_surface hginv α k)
          (surface_mem_unitInterval h01 M _ _)).map (fun z => ∑ i, (z i).2) =
      Bin(n, ⟨M.armMean ginv α F k, integral_mem_unitInterval
        (M.measurable_surface hginv α k) (surface_mem_unitInterval h01 M _ _)⟩) :=
  (map_sum_pi_compProd_bernoulli F (M.measurable_surface hginv α k)
    (surface_mem_unitInterval h01 M _ _) n).2

/-- **The binomial aggregate likelihood is the probability of the observed count**: with the
binomial summary density of arms of `n` patients, the factor of an aggregate record with count
`y` of arm `(j, k)` is the probability that the count of events of that arm equals `y`, when
the covariates of the patients are independent draws from `F_j` and the outcomes are
`Ber(g⁻¹(η_jk(x)))`. -/
theorem likelihood_cons_binomialDensity {ginv : ℝ → ℝ} (hginv : Measurable ginv)
    (h01 : ∀ y, ginv y ∈ I) (f : ℝ → ℝ → ℝ) (M : MultilevelModel J K p)
    (F : J → Measure (Fin p → ℝ)) [∀ j, IsProbabilityMeasure (F j)] (n : ℕ)
    {arms : J → Finset K} (ipd : List (ArmIndex arms × (Fin p → ℝ) × ℝ))
    (agd : List (ArmIndex arms × ℝ)) (a : ArmIndex arms) (y : ℕ) :
    M.likelihood f (binomialDensity n) ginv F ipd ((a, (y : ℝ)) :: agd) =
      ENNReal.ofReal ((Measure.pi fun _ : Fin n =>
          F a.1.1 ⊗ₘ bernoulliKernel (M.surface ginv (M.μ a.1.1) a.1.2)
            (M.measurable_surface hginv _ _) (surface_mem_unitInterval h01 M _ _)).real
          {z | ∑ i, (z i).2 = y}) *
        M.likelihood f (binomialDensity n) ginv F ipd agd := by
  have hlaw := M.map_sum_pi_compProd_eq_binomial hginv h01 (M.μ a.1.1) a.1.2 (F a.1.1) n
  have hpr : (Measure.pi fun _ : Fin n =>
          F a.1.1 ⊗ₘ bernoulliKernel (M.surface ginv (M.μ a.1.1) a.1.2)
            (M.measurable_surface hginv _ _) (surface_mem_unitInterval h01 M _ _)).real
          {z | ∑ i, (z i).2 = y} = binomialDensity n (M.armMean ginv (M.μ a.1.1) (F a.1.1) a.1.2)
            y := by
    have h := congrArg (fun ν : Measure ℕ => ν.real {y}) hlaw
    rw [map_measureReal_apply (f := fun z : Fin n → (Fin p → ℝ) × ℕ => ∑ i, (z i).2)
      (by fun_prop) (measurableSet_singleton y)] at h
    rw [show {z : Fin n → (Fin p → ℝ) × ℕ | ∑ i, (z i).2 = y} =
      (fun z => ∑ i, (z i).2) ⁻¹' {y} from rfl, h, binomial_real_singleton, binomialDensity,
      Nat.floor_natCast]
  rw [hpr]
  simp only [likelihood, List.map_cons, List.prod_cons]
  ring

end MultilevelModel

end NetworkMetaRegression

end CausalInference
