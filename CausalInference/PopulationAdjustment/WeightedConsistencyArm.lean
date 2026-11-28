/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.PopulationAdjustment.WeightedNoise
public import CausalInference.PopulationAdjustment.WeightMapMeasurable
public import CausalInference.PopulationAdjustment.WeightedConsistencyFeasible
public import CausalInference.PopulationAdjustment.WeightedContrast

/-!
# Consistency of the weighted arm mean with entropy balancing weights

The individual data are an i.i.d. sample `O i = (Xᵢ, Aᵢ, Yᵢ)` of the index trial. The weights
are the entropy balancing weights `cᵢ = balancingWeights (φ(Xⱼ) - t)ᵢ` of the pooled covariates,
fitted so that the weighted feature means equal the reported target moments `t`. The estimate of
the target mean of arm `a` is the weighted arm mean (`sampleBalancedArmMean`)

`μ̂_a = ∑ᵢ cᵢ 1{Aᵢ = a} Yᵢ / ∑ᵢ cᵢ 1{Aᵢ = a}`,

a function of the data and of `t` only.

**The decomposition.** When the weights are feasible (a probability vector with
`∑ᵢ cᵢ φ(Xᵢ) = t`) and `μ_a(x) = a₀ + bᵀφ(x)` is affine in the features, with `q = P(A = a)`,

`μ̂_a = (q (a₀ + bᵀt) + ∑ᵢ cᵢ (1{Aᵢ = a} - q) μ_a(Xᵢ) + ∑ᵢ cᵢ 1{Aᵢ = a}(Yᵢ - μ_{Aᵢ}(Xᵢ)))
  / (q + ∑ᵢ cᵢ (1{Aᵢ = a} - q))`

(`weightedArmMean_eq_noise_decomp`): a weighted average of the regression at the features, which
balance turns into `a₀ + bᵀt`, plus allocation noise and residual noise.

**Consistency** (`sampleBalancedArmMean_isConsistent`). Assume
* randomized assignment: `A` independent of `X` under the record law, with `P(A = a) > 0`;
* the regression `E[Y | X, A] = μ_A(X)` with conditional residual variance at most `σ²`, and
  `μ_a` affine in the features;
* bounded features, `‖φ(x) - t‖ ≤ B`;
* the margin condition of `WeightedConsistencyFeasible`: for some `δ > 0` and every `v` of norm
  one, `P(vᵀ(φ(X) - t) ≥ δ) ≥ δ` (a quantitative form of `t` lying in the interior of the convex
  hull of the support of the features).

Then `μ̂_a → a₀ + bᵀt` in probability. Feasibility of the sample problem with probability tending
to one and the bound `cᵢ ≤ K / n` are derived (`withProbTendingToOne_balancingWeights`); the noise
terms vanish by the weighted law of large numbers (`tendstoInMeasure_weighted_noise`), whose
coefficients are measurable by `measurable_balancingWeights_sample`. No measurability,
feasibility or convergence of the fitted weights is assumed.

When the reported moments are the feature means of a target population and `μ_a` is a
conditional mean function of `Y(a)` in the target (conditional constancy of the arm mean), the
limit is the target mean `E_*[Y(a)]` (`sampleBalancedArmMean_isConsistent_armMean`).

## Main definitions

* `sampleBalancedArmMean φ t O a n ω`.

## Main results

* `weightedArmMean_eq_noise_decomp`.
* `tendstoInMeasure_allocation_noise`, `tendstoInMeasure_residual_noise`.
* `sampleBalancedArmMean_isConsistent`, `sampleBalancedArmMean_isConsistent_armMean`.

## References

* J. E. Signorovitch and coauthors, PharmacoEconomics 28 (2010).
* J. Hainmueller, *Entropy balancing for causal effects: a multivariate reweighting method to
  produce balanced samples in observational studies*, Political Analysis 20 (2012).
* D. M. Phillippo, A. E. Ades, S. Dias, S. Palmer, K. R. Abrams and N. J. Welton, *Methods for
  population-adjusted indirect comparisons in health technology appraisal*, Medical Decision
  Making 38 (2018).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Finset
open scoped Topology ENNReal

namespace CausalInference

namespace PopulationAdjustment

open PointTreatment IndirectComparison

/-! ### The estimator and its decomposition -/

section Algebra

variable {𝒳 : Type*} {n p : ℕ}

theorem armWeights_eq_mul_armIndObs (w : Fin n → ℝ) (z : Fin n → 𝒳 × Bool × ℝ) (a : Bool)
    (i : Fin n) : armWeights w (fun i => (z i).2.1) a i = w i * armIndObs a (z i) := by
  simp only [armWeights, armIndObs]; split_ifs <;> simp

/-- **The decomposition of the weighted arm mean.** For feasible weights `c` (a probability
vector with `∑ᵢ cᵢ φ(xᵢ) = t`), an arm regression `μ_a(x) = a₀ + bᵀφ(x)` affine in the features
and any `q`, the weighted arm mean is
`(q (a₀ + bᵀt) + ∑ᵢ cᵢ (1{aᵢ = a} - q) μ_a(xᵢ) + ∑ᵢ cᵢ 1{aᵢ = a}(yᵢ - μ_{aᵢ}(xᵢ)))
  / (q + ∑ᵢ cᵢ (1{aᵢ = a} - q))`. -/
theorem weightedArmMean_eq_noise_decomp {φ : 𝒳 → Fin p → ℝ} {t : Fin p → ℝ}
    {c : Fin n → ℝ} {z : Fin n → 𝒳 × Bool × ℝ} (hc : c ∈ balancingSet fun i => φ (z i).1 - t)
    (a : Bool) {mu : Bool → 𝒳 → ℝ} {a0 : ℝ} {b : Fin p → ℝ}
    (haff : ∀ x, mu a x = a0 + b ⬝ᵥ φ x) (q : ℝ) :
    weightedArmMean c (fun i => (z i).2.1) (fun i => (z i).2.2) a =
      (q * (a0 + b ⬝ᵥ t) + ∑ i, c i * ((armIndObs a (z i) - q) * mu a (z i).1) +
          ∑ i, c i * (armIndObs a (z i) * ((z i).2.2 - mu (z i).2.1 (z i).1))) /
        (q + ∑ i, c i * ((armIndObs a (z i) - q) * 1)) := by
  obtain ⟨-, hc1, hcbal⟩ := mem_balancingSet_sub_iff.1 hc
  have hmu : ∑ i, c i * mu a (z i).1 = a0 + b ⬝ᵥ t := by
    simp only [haff, mul_add, Finset.sum_add_distrib, ← Finset.sum_mul, hc1, one_mul]
    congr 1
    rw [← hcbal, dotProduct_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [dotProduct_smul, smul_eq_mul]
  have hden : ∑ i, armWeights c (fun i => (z i).2.1) a i =
      q + ∑ i, c i * ((armIndObs a (z i) - q) * 1) := by
    simp only [armWeights_eq_mul_armIndObs, mul_one, mul_sub, Finset.sum_sub_distrib,
      ← Finset.sum_mul, hc1]
    ring
  have hterm : ∀ i, armWeights c (fun i => (z i).2.1) a i * (z i).2.2 =
      c i * ((armIndObs a (z i) - q) * mu a (z i).1) +
        c i * (armIndObs a (z i) * ((z i).2.2 - mu (z i).2.1 (z i).1)) +
        q * (c i * mu a (z i).1) := fun i => by
    rw [armWeights_eq_mul_armIndObs]
    simp only [armIndObs]
    split_ifs with h
    · rw [h]; ring
    · ring
  rw [weightedArmMean, weightedMean, hden, Finset.sum_congr rfl fun i _ => hterm i,
    Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, hmu]
  ring

end Algebra

variable {Ω 𝒳 : Type*} [MeasurableSpace Ω] [MeasurableSpace 𝒳] {p : ℕ}

/-- **The weighted (matching adjusted) arm mean** of arm `a` from the first `n` records of the
sample `O`, with the entropy balancing weights of the pooled covariates at the reported target
moments `t`: `∑ᵢ cᵢ 1{Aᵢ = a} Yᵢ / ∑ᵢ cᵢ 1{Aᵢ = a}` with `c = balancingWeights (φ(Xⱼ) - t)`. -/
noncomputable def sampleBalancedArmMean (φ : 𝒳 → Fin p → ℝ) (t : Fin p → ℝ)
    (O : ℕ → Ω → 𝒳 × Bool × ℝ) (a : Bool) (n : ℕ) (ω : Ω) : ℝ :=
  weightedArmMean (balancingWeights fun i : Fin n => φ (O i ω).1 - t) (fun i => (O i ω).2.1)
    (fun i => (O i ω).2.2) a

/-! ### Limit helpers -/

section Helpers

variable {P : Measure Ω}

/-- **Domination on events of probability tending to one.** If `|Xₙ| ≤ rₙ` on events of
probability tending to one and `rₙ → 0`, then `Xₙ → 0` in probability. -/
theorem tendstoInMeasure_zero_of_abs_le_on {X : ℕ → Ω → ℝ} {A : ℕ → Set Ω}
    (hA : WithProbTendingToOne P A) {r : ℕ → ℝ} (hr : Tendsto r atTop (𝓝 0))
    (h : ∀ n, ∀ ω ∈ A n, |X n ω| ≤ r n) : TendstoInMeasure P X atTop (fun _ => 0) := by
  refine tendstoInMeasure_of_good_events fun ε hε κ hκ => ⟨A, hA.eventually_le hκ, ?_⟩
  filter_upwards [(tendsto_order.1 hr).2 ε hε] with n hn ω hω
  rw [Real.dist_eq, sub_zero]
  exact (h n ω hω).trans_lt hn

theorem balancingWeights_nonneg {n : ℕ} (Δ : Fin n → Fin p → ℝ) (i : Fin n) :
    0 ≤ balancingWeights Δ i := by
  have : Nonempty (Fin n) := ⟨i⟩
  exact (entropyWeights_pos _ i).le

theorem balancingWeights_le_one {n : ℕ} (Δ : Fin n → Fin p → ℝ) (i : Fin n) :
    balancingWeights Δ i ≤ 1 := by
  have : Nonempty (Fin n) := ⟨i⟩
  rw [← sum_entropyWeights (Δ := Δ) (dualMinimizer Δ)]
  exact Finset.single_le_sum (fun j _ => (entropyWeights_pos _ j).le) (Finset.mem_univ i)

theorem abs_balancingWeights_le_one {n : ℕ} (Δ : Fin n → Fin p → ℝ) (i : Fin n) :
    |balancingWeights Δ i| ≤ 1 := by
  rw [abs_of_nonneg (balancingWeights_nonneg Δ i)]; exact balancingWeights_le_one Δ i

/-- For feasible weights at most `K / n` and `0 ≤ vᵢ ≤ V`, `∑ᵢ cᵢ² vᵢ ≤ V K / n`. -/
theorem sum_sq_mul_le_of_mem_balancingSet {n : ℕ} {Δ : Fin n → Fin p → ℝ} {c : Fin n → ℝ}
    (hc : c ∈ balancingSet Δ) {K : ℝ} (hcK : ∀ i, c i ≤ K / n) {v : Fin n → ℝ} {V : ℝ}
    (hv0 : ∀ i, 0 ≤ v i) (hvV : ∀ i, v i ≤ V) : ∑ i, c i ^ 2 * v i ≤ V * K / n := by
  obtain ⟨hc0, hc1, -⟩ := hc
  calc ∑ i, c i ^ 2 * v i ≤ ∑ i, c i * (K / n * V) := Finset.sum_le_sum fun i _ => by
        rw [sq, mul_assoc]
        exact mul_le_mul_of_nonneg_left (mul_le_mul (hcK i) (hvV i) (hv0 i)
          ((hc0 i).trans (hcK i))) (hc0 i)
    _ = V * K / n := by rw [← Finset.sum_mul, hc1]; ring

/-- An integrable outcome is implied by a square integrable residual of a regression: if
`E[Y | 𝓖] = μ` and `Y - μ` is square integrable, then `Y` is integrable (otherwise the
conditional expectation is `0`, so `μ = 0` and `Y = Y - μ`). -/
theorem integrable_of_condExp_eq_of_sq {D : Type*} [mD : MeasurableSpace D] {ν : Measure D}
    [IsFiniteMeasure ν] (m : MeasurableSpace D) {Y mu : D → ℝ} (hY : Measurable[mD] Y)
    (hmu : Measurable[mD] mu) (hreg : ν[Y | m] =ᵐ[ν] mu)
    (hres2 : Integrable (fun z => (Y z - mu z) ^ 2) ν) : Integrable Y ν := by
  have hR : Integrable (fun z => Y z - mu z) ν :=
    ((memLp_two_iff_integrable_sq (μ := ν) (f := fun z => Y z - mu z)
      (hY.sub hmu).aestronglyMeasurable).2 hres2).integrable one_le_two
  by_contra hY'
  have h0 : ν[Y | m] = 0 := condExp_of_not_integrable hY'
  have hmu0 : mu =ᵐ[ν] 0 := hreg.symm.trans (by rw [h0])
  exact hY' (hR.congr (hmu0.mono fun z hz => by simp [hz]))

end Helpers

/-! ### The noise terms vanish -/

section Noise

variable {P : Measure Ω} [IsProbabilityMeasure P] {O : ℕ → Ω → 𝒳 × Bool × ℝ}

/-- The feasibility event of the sample: nonempty, feasible weights at most `K / n`. -/
theorem withProbTendingToOne_balancingWeights_fst (hO : IsIIDSample O P) {φ : 𝒳 → Fin p → ℝ}
    (hφ : Measurable φ) {t : Fin p → ℝ} {B : ℝ} (hB : ∀ x, ‖φ x - t‖ ≤ B) {δ : ℝ}
    (hδ : 0 < δ) (hmargin : ∀ v : Fin p → ℝ, ‖v‖ = 1 →
      δ ≤ (P.map (O 0)).real {z | δ ≤ v ⬝ᵥ (φ z.1 - t)}) :
    WithProbTendingToOne P (fun n => {ω | 0 < n ∧
      balancingWeights (fun i : Fin n => φ (O i ω).1 - t) ∈
        balancingSet (fun i : Fin n => φ (O i ω).1 - t) ∧
      ∀ i, balancingWeights (fun i : Fin n => φ (O i ω).1 - t) i ≤
        Real.exp (2 * p * (4 / δ ^ 2) * B) / n}) :=
  withProbTendingToOne_balancingWeights hO (hφ.comp measurable_fst) (fun z => hB z.1) hδ hmargin

/-- **The weighted allocation noise vanishes.** Under randomized assignment, bounded features and
the margin condition, for a bounded measurable `ψ` the weighted allocation noise
`∑ᵢ cᵢ (1{Aᵢ = a} - q) ψ(Xᵢ)` tends to zero in probability, `q = P(A = a)`. -/
theorem tendstoInMeasure_allocation_noise (hO : IsIIDSample O P) (hOm : ∀ i, Measurable (O i))
    {φ : 𝒳 → Fin p → ℝ} (hφ : Measurable φ) {t : Fin p → ℝ} {B : ℝ} (hB : ∀ x, ‖φ x - t‖ ≤ B)
    {δ : ℝ} (hδ : 0 < δ) (hmargin : ∀ v : Fin p → ℝ, ‖v‖ = 1 →
      δ ≤ (P.map (O 0)).real {z | δ ≤ v ⬝ᵥ (φ z.1 - t)})
    (hind : IndepFun (fun z : 𝒳 × Bool × ℝ => z.1) (fun z => z.2.1) (P.map (O 0))) (a : Bool)
    {ψ : 𝒳 → ℝ} (hψ : Measurable ψ) {M : ℝ} (hψM : ∀ x, |ψ x| ≤ M) :
    TendstoInMeasure P (fun n ω => ∑ i : Fin n,
      balancingWeights (fun j : Fin n => φ (O j ω).1 - t) i *
        ((armIndObs a (O i ω) - (P.map (O 0)).real {z | z.2.1 = a}) * ψ (O i ω).1))
      atTop (fun _ => 0) := by
  set q := (P.map (O 0)).real {z : 𝒳 × Bool × ℝ | z.2.1 = a} with hq
  have hψ2 : Integrable (fun z : 𝒳 × Bool × ℝ => ψ z.1 ^ 2) (P.map (O 0)) :=
    (integrable_const (M ^ 2)).mono' ((hψ.comp measurable_fst).pow_const 2).aestronglyMeasurable
      (ae_of_all _ fun z => by
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), ← sq_abs]
        exact pow_le_pow_left₀ (abs_nonneg _) (hψM _) 2)
  obtain ⟨hmean, hvar⟩ := allocation_noise_moments hind a hψ hψ2
  have he : Measurable fun z : 𝒳 × Bool × ℝ => (armIndObs a z - q) * ψ z.1 :=
    ((measurable_armIndObs a).sub_const q).mul (hψ.comp measurable_fst)
  have he2 : Integrable (fun z : 𝒳 × Bool × ℝ => ((armIndObs a z - q) * ψ z.1) ^ 2)
      (P.map (O 0)) :=
    hψ2.mono' (he.pow_const 2).aestronglyMeasurable (ae_of_all _ fun z => by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), mul_pow]
      exact mul_le_of_le_one_left (sq_nonneg _)
        ((sq_le_one_iff_abs_le_one _).2 (abs_armIndObs_sub_le_one a z)))
  have ha : ∀ n (i : Fin n), Measurable fun x : Fin n → 𝒳 =>
      balancingWeights (fun j => φ (x j) - t) i := fun n i =>
    (measurable_pi_apply i).comp (measurable_balancingWeights_sample hφ t)
  refine tendstoInMeasure_weighted_noise (C := fun z : 𝒳 × Bool × ℝ => z.1) hO hOm measurable_fst
    he he2 hmean (hψ.pow_const 2) (fun _ => sq_nonneg _) hψ2 hvar
    (fun n i x => balancingWeights (fun j => φ (x j) - t) i) ha
    (fun n i x => abs_balancingWeights_le_one _ i) ?_
  refine tendstoInMeasure_zero_of_abs_le_on (withProbTendingToOne_balancingWeights_fst hO hφ hB hδ
    hmargin) (r := fun n => M ^ 2 * Real.exp (2 * p * (4 / δ ^ 2) * B) / n) ?_ ?_
  · exact tendsto_const_div_atTop_nhds_zero_nat (M ^ 2 * Real.exp (2 * p * (4 / δ ^ 2) * B))
  · rintro n ω ⟨-, hc, hcK⟩
    rw [abs_of_nonneg (Finset.sum_nonneg fun i _ => mul_nonneg (sq_nonneg _) (sq_nonneg _))]
    refine sum_sq_mul_le_of_mem_balancingSet hc hcK (fun i => sq_nonneg _) fun i => ?_
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (hψM _) 2

omit [IsProbabilityMeasure P] in
/-- The surface `(x, s) ↦ μ_s(x)` of a family of measurable arm regressions is measurable. -/
theorem measurable_regression_surface {mu : Bool → 𝒳 → ℝ} (hmu : ∀ s, Measurable (mu s)) :
    Measurable fun z : 𝒳 × Bool × ℝ => mu z.2.1 z.1 :=
  (measurable_from_prod_countable_left (f := fun q : 𝒳 × Bool => mu q.2 q.1) hmu).comp
    (measurable_fst.prodMk measurable_snd.fst)

/-- **The weighted residual noise vanishes.** Under the regression `E[Y | X, A] = μ_A(X)` with a
square integrable residual of conditional variance at most `σ²`, bounded features and the margin
condition, `∑ᵢ cᵢ 1{Aᵢ = a}(Yᵢ - μ_{Aᵢ}(Xᵢ))` tends to zero in probability. -/
theorem tendstoInMeasure_residual_noise (hO : IsIIDSample O P) (hOm : ∀ i, Measurable (O i))
    {φ : 𝒳 → Fin p → ℝ} (hφ : Measurable φ) {t : Fin p → ℝ} {B : ℝ} (hB : ∀ x, ‖φ x - t‖ ≤ B)
    {δ : ℝ} (hδ : 0 < δ) (hmargin : ∀ v : Fin p → ℝ, ‖v‖ = 1 →
      δ ≤ (P.map (O 0)).real {z | δ ≤ v ⬝ᵥ (φ z.1 - t)}) (a : Bool)
    {mu : Bool → 𝒳 → ℝ} (hmu : ∀ s, Measurable (mu s))
    (hres2 : Integrable (fun z : 𝒳 × Bool × ℝ => (z.2.2 - mu z.2.1 z.1) ^ 2) (P.map (O 0)))
    (hreg : (P.map (O 0))[fun z => z.2.2 | MeasurableSpace.comap
      (fun z : 𝒳 × Bool × ℝ => (z.1, z.2.1)) inferInstance] =ᵐ[P.map (O 0)]
        fun z => mu z.2.1 z.1) {σ2 : ℝ}
    (hvar : (P.map (O 0))[fun z => (z.2.2 - mu z.2.1 z.1) ^ 2 |
      MeasurableSpace.comap (fun z : 𝒳 × Bool × ℝ => (z.1, z.2.1)) inferInstance]
        ≤ᵐ[P.map (O 0)] fun _ => σ2) :
    TendstoInMeasure P (fun n ω => ∑ i : Fin n,
      balancingWeights (fun j : Fin n => φ (O j ω).1 - t) i *
        (armIndObs a (O i ω) * ((O i ω).2.2 - mu (O i ω).2.1 (O i ω).1)))
      atTop (fun _ => 0) := by
  have hS := measurable_regression_surface hmu
  have hY : Integrable (fun z : 𝒳 × Bool × ℝ => z.2.2) (P.map (O 0)) :=
    integrable_of_condExp_eq_of_sq _ measurable_snd.snd hS hreg hres2
  obtain ⟨hmean, hvar'⟩ := residual_noise_moments a hmu hY hres2 hreg hvar
  have he : Measurable fun z : 𝒳 × Bool × ℝ => armIndObs a z * (z.2.2 - mu z.2.1 z.1) :=
    (measurable_armIndObs a).mul (measurable_snd.snd.sub hS)
  have he2 : Integrable (fun z : 𝒳 × Bool × ℝ => (armIndObs a z * (z.2.2 - mu z.2.1 z.1)) ^ 2)
      (P.map (O 0)) :=
    hres2.mono' (he.pow_const 2).aestronglyMeasurable (ae_of_all _ fun z => by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), mul_pow]
      refine mul_le_of_le_one_left (sq_nonneg _) ?_
      rcases armIndObs_eq_zero_or_one a z with h | h <;> rw [h] <;> norm_num)
  have ha : ∀ n (i : Fin n), Measurable fun c : Fin n → 𝒳 × Bool =>
      balancingWeights (fun j => φ (c j).1 - t) i := fun n i => by
    have h1 : Measurable fun c : Fin n → 𝒳 × Bool => fun j => (c j).1 :=
      Measurable.of_eval fun j => (measurable_pi_apply j).fst
    exact (measurable_pi_apply i).comp ((measurable_balancingWeights_sample hφ t).comp h1)
  refine tendstoInMeasure_weighted_noise (C := fun z : 𝒳 × Bool × ℝ => (z.1, z.2.1)) hO hOm
    (measurable_fst.prodMk measurable_snd.fst) he he2 hmean (v := fun _ => max σ2 0)
    measurable_const (fun _ => le_max_right _ _) (integrable_const _) hvar'
    (fun n i c => balancingWeights (fun j => φ (c j).1 - t) i) ha
    (fun n i c => abs_balancingWeights_le_one _ i) ?_
  refine tendstoInMeasure_zero_of_abs_le_on (withProbTendingToOne_balancingWeights_fst hO hφ hB hδ
    hmargin) (r := fun n => max σ2 0 * Real.exp (2 * p * (4 / δ ^ 2) * B) / n)
    (tendsto_const_div_atTop_nhds_zero_nat _) ?_
  rintro n ω ⟨-, hc, hcK⟩
  rw [abs_of_nonneg (Finset.sum_nonneg fun i _ => mul_nonneg (sq_nonneg _) (le_max_right _ _))]
  exact sum_sq_mul_le_of_mem_balancingSet hc hcK (fun i => le_max_right _ _) fun i => le_rfl

end Noise

/-! ### Affine regressions -/

/-- **The target mean of an affine function of the features** is the affine function of the
reported moments: for bounded measurable features with means `t` under the covariate law of a
probability population, `∫ (a₀ + bᵀφ) dQ_X = a₀ + bᵀt`. -/
theorem integral_affine_covLaw {Ω' ι : Type*} [MeasurableSpace Ω'] {Q : Population Ω' 𝒳 ι}
    [IsProbabilityMeasure Q.μ] {φ : 𝒳 → Fin p → ℝ} (hφ : Measurable φ) {t : Fin p → ℝ} {B : ℝ}
    (hB : ∀ x, ‖φ x - t‖ ≤ B) (ht : ∀ k, ∫ x, φ x k ∂Q.covLaw = t k) {f : 𝒳 → ℝ} {a0 : ℝ}
    {b : Fin p → ℝ} (haff : ∀ x, f x = a0 + b ⬝ᵥ φ x) : ∫ x, f x ∂Q.covLaw = a0 + b ⬝ᵥ t := by
  have : IsProbabilityMeasure Q.covLaw := by unfold Population.covLaw; infer_instance
  have hφk : ∀ k, Integrable (fun x => φ x k) Q.covLaw := fun k =>
    (integrable_const (B + ‖t‖)).mono' ((measurable_pi_apply k).comp hφ).aestronglyMeasurable
      (ae_of_all _ fun x => by
        calc ‖φ x k‖ ≤ ‖φ x‖ := norm_le_pi_norm (φ x) k
          _ = ‖(φ x - t) + t‖ := by rw [sub_add_cancel]
          _ ≤ B + ‖t‖ := (norm_add_le _ _).trans (by linarith [hB x]))
  simp only [haff, dotProduct]
  rw [integral_add (integrable_const _) (integrable_finsetSum _ fun k _ =>
    (hφk k).const_mul (b k)), integral_const, integral_finsetSum _ fun k _ =>
    (hφk k).const_mul (b k)]
  simp only [probReal_univ, one_smul, integral_const_mul, ht]

/-- Arm regressions affine in measurable features are measurable. -/
theorem measurable_regressions_of_affine {φ : 𝒳 → Fin p → ℝ} (hφ : Measurable φ)
    {mu : Bool → 𝒳 → ℝ} {a0A a0C : ℝ} {bA bC : Fin p → ℝ}
    (haffA : ∀ x, mu true x = a0A + bA ⬝ᵥ φ x) (haffC : ∀ x, mu false x = a0C + bC ⬝ᵥ φ x) :
    ∀ s, Measurable (mu s) := by
  intro s
  cases s
  · rw [show mu false = fun x => a0C + bC ⬝ᵥ φ x from funext haffC]
    exact measurable_const.add ((continuous_const.dotProduct continuous_id).measurable.comp hφ)
  · rw [show mu true = fun x => a0A + bA ⬝ᵥ φ x from funext haffA]
    exact measurable_const.add ((continuous_const.dotProduct continuous_id).measurable.comp hφ)

/-! ### Consistency of the weighted arm mean -/

section Consistency

variable {P : Measure Ω} [IsProbabilityMeasure P] {O : ℕ → Ω → 𝒳 × Bool × ℝ}

/-- **Consistency of the weighted (matching adjusted) arm mean.** Let `O` be an i.i.d. sample of
index trial records `(X, A, Y)` with measurable coordinates, and assume:
* randomized assignment: `A` is independent of `X` under the record law, and `P(A = a) > 0`;
* the regression `E[Y | X, A] = μ_A(X)` with measurable arm regressions, a square integrable
  residual and conditional residual variance at most `σ²`;
* the regression of arm `a` is affine in the matched features, `μ_a(x) = a₀ + bᵀφ(x)`;
* bounded features, `‖φ(x) - t‖ ≤ B`, with `φ` measurable;
* the margin condition at the reported target moments `t`: for some `δ > 0` and every `v` of sup
  norm one, `P(vᵀ(φ(X) - t) ≥ δ) ≥ δ`.

Then the weighted arm mean with the entropy balancing weights at `t` is consistent for
`a₀ + bᵀt`. Sample feasibility holds with probability tending to one
(`withProbTendingToOne_balancingWeights`); it is not assumed. -/
theorem sampleBalancedArmMean_isConsistent (hO : IsIIDSample O P) (hOm : ∀ i, Measurable (O i))
    {φ : 𝒳 → Fin p → ℝ} (hφ : Measurable φ) {t : Fin p → ℝ} {B : ℝ} (hB : ∀ x, ‖φ x - t‖ ≤ B)
    {δ : ℝ} (hδ : 0 < δ) (hmargin : ∀ v : Fin p → ℝ, ‖v‖ = 1 →
      δ ≤ (P.map (O 0)).real {z | δ ≤ v ⬝ᵥ (φ z.1 - t)})
    (hind : IndepFun (fun z : 𝒳 × Bool × ℝ => z.1) (fun z => z.2.1) (P.map (O 0))) (a : Bool)
    (hq : 0 < (P.map (O 0)).real {z | z.2.1 = a})
    {mu : Bool → 𝒳 → ℝ} (hmu : ∀ s, Measurable (mu s))
    (hres2 : Integrable (fun z : 𝒳 × Bool × ℝ => (z.2.2 - mu z.2.1 z.1) ^ 2) (P.map (O 0)))
    (hreg : (P.map (O 0))[fun z => z.2.2 | MeasurableSpace.comap
      (fun z : 𝒳 × Bool × ℝ => (z.1, z.2.1)) inferInstance] =ᵐ[P.map (O 0)]
        fun z => mu z.2.1 z.1) {σ2 : ℝ}
    (hvar : (P.map (O 0))[fun z => (z.2.2 - mu z.2.1 z.1) ^ 2 |
      MeasurableSpace.comap (fun z : 𝒳 × Bool × ℝ => (z.1, z.2.1)) inferInstance]
        ≤ᵐ[P.map (O 0)] fun _ => σ2)
    {a0 : ℝ} {b : Fin p → ℝ} (haff : ∀ x, mu a x = a0 + b ⬝ᵥ φ x) :
    IsConsistent (sampleBalancedArmMean φ t O a) (a0 + b ⬝ᵥ t) P := by
  set q := (P.map (O 0)).real {z : 𝒳 × Bool × ℝ | z.2.1 = a} with hqdef
  set L := a0 + b ⬝ᵥ t with hL
  have hM : ∀ x, |mu a x| ≤ |a0| + p * (‖b‖ * B) + |b ⬝ᵥ t| := fun x => by
    have h1 : mu a x = a0 + b ⬝ᵥ (φ x - t) + b ⬝ᵥ t := by
      rw [haff, dotProduct_sub]; ring
    rw [h1]
    have h2 : |b ⬝ᵥ (φ x - t)| ≤ p * (‖b‖ * B) :=
      (abs_dotProduct_le_mul_norm b _).trans (mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left (hB x) (norm_nonneg _)) (Nat.cast_nonneg p))
    calc |a0 + b ⬝ᵥ (φ x - t) + b ⬝ᵥ t| ≤ |a0 + b ⬝ᵥ (φ x - t)| + |b ⬝ᵥ t| := abs_add_le _ _
      _ ≤ |a0| + |b ⬝ᵥ (φ x - t)| + |b ⬝ᵥ t| := by gcongr; exact abs_add_le _ _
      _ ≤ |a0| + p * (‖b‖ * B) + |b ⬝ᵥ t| := by gcongr
  have hN1 := tendstoInMeasure_allocation_noise hO hOm hφ hB hδ hmargin hind a
    (ψ := fun _ => (1 : ℝ)) measurable_const (M := 1) (fun _ => by norm_num)
  have hN2 := tendstoInMeasure_allocation_noise hO hOm hφ hB hδ hmargin hind a (hmu a) hM
  have hN3 := tendstoInMeasure_residual_noise hO hOm hφ hB hδ hmargin a hmu hres2 hreg hvar
  set G : ℝ × ℝ × ℝ → ℝ := fun u => (q * L + u.2.1 + u.2.2) / (q + u.1) with hG
  have hGc : ContinuousAt G (0, 0, 0) := by
    refine ContinuousAt.div (by fun_prop) (by fun_prop) ?_
    simpa using hq.ne'
  have hlim := (hN1.prodMk (hN2.prodMk hN3)).comp_continuousAt hGc
  have hG0 : G (0, 0, 0) = L := by
    simp only [hG, add_zero]; field_simp
  rw [hG0] at hlim
  refine hlim.congr_withProbTendingToOne (withProbTendingToOne_balancingWeights_fst hO hφ hB hδ
    hmargin) ?_
  rintro n ω ⟨-, hc, -⟩
  rw [sampleBalancedArmMean, weightedArmMean_eq_noise_decomp (z := fun i => O i ω) hc a haff q]

/-- **The limit is the target mean of the arm.** In addition to the assumptions of
`sampleBalancedArmMean_isConsistent`, let `Q` be a target population whose covariate law is a
probability measure, whose feature means are the reported moments `t`, and in which `μ_a` is a
conditional mean function of the integrable outcome `Y(a)` (conditional constancy of the arm
regression). Then the weighted arm mean is consistent for the target arm mean `E_Q[Y(a)]`. -/
theorem sampleBalancedArmMean_isConsistent_armMean {Ω' ι : Type*} [MeasurableSpace Ω']
    (hO : IsIIDSample O P) (hOm : ∀ i, Measurable (O i))
    {φ : 𝒳 → Fin p → ℝ} (hφ : Measurable φ) {t : Fin p → ℝ} {B : ℝ} (hB : ∀ x, ‖φ x - t‖ ≤ B)
    {δ : ℝ} (hδ : 0 < δ) (hmargin : ∀ v : Fin p → ℝ, ‖v‖ = 1 →
      δ ≤ (P.map (O 0)).real {z | δ ≤ v ⬝ᵥ (φ z.1 - t)})
    (hind : IndepFun (fun z : 𝒳 × Bool × ℝ => z.1) (fun z => z.2.1) (P.map (O 0))) (a : Bool)
    (hq : 0 < (P.map (O 0)).real {z | z.2.1 = a})
    {mu : Bool → 𝒳 → ℝ} (hmu : ∀ s, Measurable (mu s))
    (hres2 : Integrable (fun z : 𝒳 × Bool × ℝ => (z.2.2 - mu z.2.1 z.1) ^ 2) (P.map (O 0)))
    (hreg : (P.map (O 0))[fun z => z.2.2 | MeasurableSpace.comap
      (fun z : 𝒳 × Bool × ℝ => (z.1, z.2.1)) inferInstance] =ᵐ[P.map (O 0)]
        fun z => mu z.2.1 z.1) {σ2 : ℝ}
    (hvar : (P.map (O 0))[fun z => (z.2.2 - mu z.2.1 z.1) ^ 2 |
      MeasurableSpace.comap (fun z : 𝒳 × Bool × ℝ => (z.1, z.2.1)) inferInstance]
        ≤ᵐ[P.map (O 0)] fun _ => σ2)
    {a0 : ℝ} {b : Fin p → ℝ} (haff : ∀ x, mu a x = a0 + b ⬝ᵥ φ x)
    {Q : Population Ω' 𝒳 ι} [IsProbabilityMeasure Q.μ] (hQX : Measurable Q.X)
    (ht : ∀ k, ∫ x, φ x k ∂Q.covLaw = t k) {ta : ι} (hQY : Integrable (Q.Y ta) Q.μ)
    (hQm : Q.IsCondMean ta (mu a)) :
    IsConsistent (sampleBalancedArmMean φ t O a) (Q.armMean ta) P := by
  have hint := integral_affine_covLaw hφ hB ht haff
  rw [← hQm.integral_eq hQX hQY, hint]
  exact sampleBalancedArmMean_isConsistent hO hOm hφ hB hδ hmargin hind a hq hmu hres2 hreg hvar
    haff

end Consistency

/-! ### The index trial -/

section Trial

omit [MeasurableSpace 𝒳] in
/-- Independence of two functions of a variable under its law is independence of the composed
functions. -/
theorem indepFun_map_iff {β γ κ : Type*} [MeasurableSpace β] [MeasurableSpace γ]
    [MeasurableSpace κ] {μ : Measure Ω} {f : Ω → β} (hf : Measurable f) {g : β → γ}
    {h : β → κ} (hg : Measurable g) (hh : Measurable h) :
    IndepFun g h (μ.map f) ↔ IndepFun (g ∘ f) (h ∘ f) μ := by
  rw [indepFun_iff_measure_inter_preimage_eq_mul, indepFun_iff_measure_inter_preimage_eq_mul]
  refine forall₂_congr fun s u => imp_congr_right fun hs => imp_congr_right fun hu => ?_
  rw [Measure.map_apply hf ((hg hs).inter (hh hu)), Measure.map_apply hf (hg hs),
    Measure.map_apply hf (hh hu)]
  rfl

variable {Ω₁ : Type*} [MeasurableSpace Ω₁] {P : Measure Ω} [IsProbabilityMeasure P]
  {O : ℕ → Ω → 𝒳 × Bool × ℝ}

/-- **Consistency of the weighted arm mean for the individual data of a randomized trial.** Let
`T` be a trial with measurable covariates, assignment and observed outcome, randomized in the
sense that the assignment is independent of the covariates, and let `O` be an i.i.d. sample of
its individual data (`P.map (O 0) = T.ipdLaw`). Assume `P(A = a) > 0`, bounded features, the
margin condition for the covariate law of the trial at the reported moments `t`, and, for the
observed outcome, the regression `E[Y | X, A] = μ_A(X)` with a square integrable residual of
bounded conditional variance and `μ_a = a₀ + bᵀφ`. Then the weighted arm mean is consistent for
`a₀ + bᵀt`. Independence of covariates and arm in the individual data law is derived from the
randomization of the trial. -/
theorem sampleBalancedArmMean_isConsistent_trial {T : Trial Ω₁ 𝒳 Bool} (hX : Measurable T.X)
    (hA : Measurable T.A) (hYo : Measurable T.obsOutcome) (hrand : IndepFun T.X T.A T.μ)
    (hO : IsIIDSample O P) (hOm : ∀ i, Measurable (O i)) (hlaw : P.map (O 0) = T.ipdLaw)
    {φ : 𝒳 → Fin p → ℝ} (hφ : Measurable φ) {t : Fin p → ℝ} {B : ℝ} (hB : ∀ x, ‖φ x - t‖ ≤ B)
    {δ : ℝ} (hδ : 0 < δ)
    (hmargin : ∀ v : Fin p → ℝ, ‖v‖ = 1 → δ ≤ T.covLaw.real {x | δ ≤ v ⬝ᵥ (φ x - t)})
    (a : Bool) (hq : 0 < T.μ.real (T.A ⁻¹' {a}))
    {mu : Bool → 𝒳 → ℝ} (hmu : ∀ s, Measurable (mu s))
    (hres2 : Integrable (fun z : 𝒳 × Bool × ℝ => (z.2.2 - mu z.2.1 z.1) ^ 2) T.ipdLaw)
    (hreg : T.ipdLaw[fun z => z.2.2 | MeasurableSpace.comap
      (fun z : 𝒳 × Bool × ℝ => (z.1, z.2.1)) inferInstance] =ᵐ[T.ipdLaw]
        fun z => mu z.2.1 z.1) {σ2 : ℝ}
    (hvar : T.ipdLaw[fun z => (z.2.2 - mu z.2.1 z.1) ^ 2 |
      MeasurableSpace.comap (fun z : 𝒳 × Bool × ℝ => (z.1, z.2.1)) inferInstance]
        ≤ᵐ[T.ipdLaw] fun _ => σ2)
    {a0 : ℝ} {b : Fin p → ℝ} (haff : ∀ x, mu a x = a0 + b ⬝ᵥ φ x) :
    IsConsistent (sampleBalancedArmMean φ t O a) (a0 + b ⬝ᵥ t) P := by
  have hf : Measurable fun ω => (T.X ω, T.A ω, T.obsOutcome ω) := hX.prodMk (hA.prodMk hYo)
  have hind : IndepFun (fun z : 𝒳 × Bool × ℝ => z.1) (fun z => z.2.1) T.ipdLaw :=
    (indepFun_map_iff hf measurable_fst measurable_snd.fst).2 hrand
  have hset : ∀ v : Fin p → ℝ, MeasurableSet {x : 𝒳 | δ ≤ v ⬝ᵥ (φ x - t)} := fun v =>
    measurableSet_le measurable_const
      ((continuous_const.dotProduct continuous_id).measurable.comp (hφ.sub_const t))
  have hmargin' : ∀ v : Fin p → ℝ, ‖v‖ = 1 →
      δ ≤ T.ipdLaw.real {z | δ ≤ v ⬝ᵥ (φ z.1 - t)} := fun v hv => by
    rw [Trial.ipdLaw, map_measureReal_apply hf
      (show MeasurableSet {z : 𝒳 × Bool × ℝ | δ ≤ v ⬝ᵥ (φ z.1 - t)} from measurable_fst (hset v))]
    have h := hmargin v hv
    rwa [Population.covLaw, map_measureReal_apply hX (hset v)] at h
  have hq' : 0 < T.ipdLaw.real {z | z.2.1 = a} := by
    rw [Trial.ipdLaw, map_measureReal_apply hf
      (measurableSet_eq_fun measurable_snd.fst measurable_const)]
    exact hq
  rw [← hlaw] at hind hmargin' hq' hres2 hreg hvar
  exact sampleBalancedArmMean_isConsistent hO hOm hφ hB hδ hmargin' hind a hq' hmu hres2 hreg
    hvar haff

end Trial

end PopulationAdjustment

end CausalInference
