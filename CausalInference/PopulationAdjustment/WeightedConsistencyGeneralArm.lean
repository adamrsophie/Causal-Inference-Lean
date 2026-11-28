/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.PopulationAdjustment.WeightedConsistencyGeneralNoise
public import CausalInference.PopulationAdjustment.WeightedConsistencyGeneralFeasible
public import CausalInference.PopulationAdjustment.WeightedConsistencyGeneralInterior

/-!
# Consistency of the weighted arm mean at converging and random targets

The weighted (matching adjusted) arm mean `sampleBalancedArmMean φ s O a n ω` uses the entropy
balancing weights of the pooled covariates at reported target moments `s`. This file proves its
consistency when the reported targets `tₙ` converge to `t` (deterministic sequences, or random
targets computed from data `W` independent of the index sample, such as the aggregate summary of
a second sample), for features that need not be bounded, and with hypotheses on the reweighted
arm `a` only.

**The general theorem** (`sampleBalancedArmMean_isConsistent_of_dispersion`) takes the two
properties of the weights as named conditions holding with probability tending to one:
feasibility (`balancingFeasibleEvent`) and vanishing dispersion
(`BalancingDispersionVanishes`). On the feasibility event the decomposition
`weightedArmMean_eq_noise_decomp` at the target `tₙ` writes the estimate as
`(q (a₀ + bᵀtₙ) + N₂ + N₃) / (q + N₁)` with allocation noise `N₁, N₂` and residual noise `N₃`,
which vanish by the weighted law of large numbers with outside data
(`tendstoInMeasure_weighted_noise_of_indepFun`), the dispersion controlling the conditional
variances (at most `K (1 + ‖φ(X) - t‖²)`).

**The conditions derived.** Under the margin condition at `t` (equivalently, the interior
condition of `WeightedConsistencyGeneralInterior`) and a finite exponential moment
`E[exp(κ ‖φ(X) - t‖)]` with `κ = 2 p (16 / δ²) + 1`, both conditions hold
(`withProbTendingToOne_balancingFeasible`, `balancingDispersionVanishes_of_integrable_exp`),
which gives `sampleBalancedArmMean_isConsistent_of_integrable_exp`. Under the interior condition
the margin is not explicit, so the moment hypothesis is taken for all orders
(`sampleBalancedArmMean_isConsistent_of_interior_of_integrable_exp`). Features bounded almost
surely and deterministic targets are special cases
(`sampleBalancedArmMean_isConsistent_of_tendsto`).

**Which regression is needed.** Only the regression `m` of arm `a` enters: its residual
`1{A = a}(Y - m(X))` is the residual noise of the weighted mean of arm `a`. The hypotheses are
`E[1{A = a} Y | X, A] = 1{A = a} m(X)`, a square integrable residual on the arm, and a bounded
conditional variance on the arm. Measurability of `m` follows from `m = a₀ + bᵀφ`; nothing is
assumed about the regression of the other arm.

## Main results

* `tendstoInMeasure_balanced_alloc_noise`, `tendstoInMeasure_balanced_residual_noise`.
* `sampleBalancedArmMean_isConsistent_of_dispersion`: the general theorem.
* `sampleBalancedArmMean_isConsistent_of_integrable_exp`: random targets, unbounded features.
* `sampleBalancedArmMean_isConsistent_of_interior_of_integrable_exp`.
* `sampleBalancedArmMean_isConsistent_of_tendsto`: deterministic targets `tₙ → t`, features
  bounded almost surely, the interior condition.

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

variable {Ω 𝒳 𝒲 : Type*} [MeasurableSpace Ω] [MeasurableSpace 𝒳] [MeasurableSpace 𝒲] {p : ℕ}
  {P : Measure Ω} [IsProbabilityMeasure P] {O : ℕ → Ω → 𝒳 × Bool × ℝ}

omit [MeasurableSpace 𝒳] in
/-- An affine function of the features is bounded by `K (1 + ‖φ(x) - t‖²)` in square, with
`K = 2 (a₀ + bᵀt)² + 2 (p ‖b‖)²`. -/
theorem sq_affine_features_le (φ : 𝒳 → Fin p → ℝ) (t : Fin p → ℝ) (a0 : ℝ) (b : Fin p → ℝ) (x : 𝒳) :
    (a0 + b ⬝ᵥ φ x) ^ 2 ≤
      (2 * (a0 + b ⬝ᵥ t) ^ 2 + 2 * (p * ‖b‖) ^ 2) * (1 + ‖φ x - t‖ ^ 2) := by
  have h1 : a0 + b ⬝ᵥ φ x = (a0 + b ⬝ᵥ t) + b ⬝ᵥ (φ x - t) := by rw [dotProduct_sub]; ring
  have h2 : |b ⬝ᵥ (φ x - t)| ≤ p * ‖b‖ * ‖φ x - t‖ := by
    rw [mul_assoc]; exact abs_dotProduct_le_mul_norm b _
  have h3 : (b ⬝ᵥ (φ x - t)) ^ 2 ≤ (p * ‖b‖) ^ 2 * ‖φ x - t‖ ^ 2 := by
    rw [← mul_pow, ← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) h2 2
  rw [h1]
  nlinarith [sq_nonneg ((a0 + b ⬝ᵥ t) - b ⬝ᵥ (φ x - t)), sq_nonneg (a0 + b ⬝ᵥ t),
    sq_nonneg (p * ‖b‖), sq_nonneg ‖φ x - t‖, mul_nonneg (sq_nonneg (a0 + b ⬝ᵥ t))
      (sq_nonneg ‖φ x - t‖)]

/-- The entropy balancing weights at random targets `T n w` are a measurable function of the
features of the sample and of the outside data. -/
theorem measurable_balancingWeights_outside {𝒞 : Type*} [MeasurableSpace 𝒞] {φ : 𝒳 → Fin p → ℝ}
    (hφ : Measurable φ) {π : 𝒞 → 𝒳} (hπ : Measurable π) {T : ℕ → 𝒲 → Fin p → ℝ}
    (hT : ∀ n, Measurable (T n)) (n : ℕ) (i : Fin n) :
    Measurable fun q : (Fin n → 𝒞) × 𝒲 =>
      balancingWeights (fun j : Fin n => φ (π (q.1 j)) - T n q.2) i := by
  have h : Measurable fun q : (Fin n → 𝒞) × 𝒲 => fun j : Fin n => φ (π (q.1 j)) - T n q.2 :=
    Measurable.of_eval fun j =>
      (hφ.comp (hπ.comp ((measurable_pi_apply j).comp measurable_fst))).sub
        ((hT n).comp measurable_snd)
  exact (measurable_pi_apply i).comp (measurable_balancingWeights.comp h)

/-- **Allocation noise of the balanced weights vanishes.** For a feature `ψ` with
`ψ(x)² ≤ K (1 + ‖φ(x) - t‖²)`, randomized assignment, square integrable features and vanishing
dispersion, the weighted allocation noise `∑ᵢ cₙᵢ (1{Aᵢ = a} - q) ψ(Xᵢ)` tends to zero in
probability, for weights at random targets computed from data independent of the sample. -/
theorem tendstoInMeasure_balanced_alloc_noise (hO : IsIIDSample O P)
    (hOm : ∀ i, Measurable (O i)) {φ : 𝒳 → Fin p → ℝ} (hφ : Measurable φ) {t : Fin p → ℝ}
    {W : Ω → 𝒲} (hW : Measurable W) (hWO : IndepFun W (fun ω k => O k ω) P)
    {T : ℕ → 𝒲 → Fin p → ℝ} (hT : ∀ n, Measurable (T n))
    (hdisp : BalancingDispersionVanishes P (fun z => φ z.1) t O fun n ω => T n (W ω))
    (hφ2 : Integrable (fun z : 𝒳 × Bool × ℝ => ‖φ z.1 - t‖ ^ 2) (P.map (O 0)))
    (hind : IndepFun (fun z : 𝒳 × Bool × ℝ => z.1) (fun z => z.2.1) (P.map (O 0))) (a : Bool)
    {ψ : 𝒳 → ℝ} (hψ : Measurable ψ) {K : ℝ}
    (hψK : ∀ x, ψ x ^ 2 ≤ K * (1 + ‖φ x - t‖ ^ 2)) :
    TendstoInMeasure P (fun n ω => ∑ i : Fin n,
      balancingWeights (fun j : Fin n => φ (O j ω).1 - T n (W ω)) i *
        ((armIndObs a (O i ω) - (P.map (O 0)).real {z | z.2.1 = a}) * ψ (O i ω).1))
      atTop (fun _ => 0) := by
  have hψ2 : Integrable (fun z : 𝒳 × Bool × ℝ => ψ z.1 ^ 2) (P.map (O 0)) :=
    (((integrable_const (1 : ℝ)).add hφ2).const_mul K).mono'
      ((hψ.comp measurable_fst).pow_const 2).aestronglyMeasurable
      (ae_of_all _ fun z => by
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]; exact hψK _)
  obtain ⟨hmean, hvar⟩ := allocation_noise_moments hind a hψ hψ2
  have he : Measurable fun z : 𝒳 × Bool × ℝ =>
      (armIndObs a z - (P.map (O 0)).real {z | z.2.1 = a}) * ψ z.1 :=
    ((measurable_armIndObs a).sub_const _).mul (hψ.comp measurable_fst)
  have he2 : Integrable (fun z : 𝒳 × Bool × ℝ =>
      ((armIndObs a z - (P.map (O 0)).real {z | z.2.1 = a}) * ψ z.1) ^ 2) (P.map (O 0)) :=
    hψ2.mono' (he.pow_const 2).aestronglyMeasurable (ae_of_all _ fun z => by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), mul_pow]
      exact mul_le_of_le_one_left (sq_nonneg _)
        ((sq_le_one_iff_abs_le_one _).2 (abs_armIndObs_sub_le_one a z)))
  have hD : TendstoInMeasure P (fun n ω => ∑ i : Fin n,
      balancingWeights (fun j : Fin n => φ (O j ω).1 - T n (W ω)) i ^ 2 * ψ (O i ω).1 ^ 2)
      atTop (fun _ => 0) := by
    have h := hdisp.const_mul K
    simp only [mul_zero] at h
    refine h.of_norm_le (Eventually.of_forall fun n ω => ?_)
    rw [Real.norm_eq_abs, Real.norm_eq_abs, Finset.mul_sum]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ((Finset.sum_le_sum fun i _ => ?_).trans
      (le_abs_self _))
    rw [abs_of_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _)), mul_left_comm]
    exact mul_le_mul_of_nonneg_left (hψK _) (sq_nonneg _)
  exact tendstoInMeasure_weighted_noise_of_indepFun (O := O)
    (C := fun z : 𝒳 × Bool × ℝ => z.1)
    (e := fun z => (armIndObs a z - (P.map (O 0)).real {z | z.2.1 = a}) * ψ z.1)
    (v := fun x => ψ x ^ 2) (W := W) hO hOm hW hWO measurable_fst he he2 hmean
    (hψ.pow_const 2) (fun _ => sq_nonneg _) hψ2 hvar
    (fun n i q' => balancingWeights (fun j : Fin n => φ (q'.1 j) - T n q'.2) i)
    (fun n i => measurable_balancingWeights_outside hφ measurable_id hT n i)
    (fun n i _ => abs_balancingWeights_le_one _ i) hD

/-- **Residual noise of arm `a` vanishes.** Under the arm `a` regression, a square integrable
residual on the arm with bounded conditional variance, and vanishing dispersion, the weighted
residual noise `∑ᵢ cₙᵢ 1{Aᵢ = a} (Yᵢ - m(Xᵢ))` tends to zero in probability. -/
theorem tendstoInMeasure_balanced_residual_noise (hO : IsIIDSample O P)
    (hOm : ∀ i, Measurable (O i)) {φ : 𝒳 → Fin p → ℝ} (hφ : Measurable φ) {t : Fin p → ℝ}
    {W : Ω → 𝒲} (hW : Measurable W) (hWO : IndepFun W (fun ω k => O k ω) P)
    {T : ℕ → 𝒲 → Fin p → ℝ} (hT : ∀ n, Measurable (T n))
    (hdisp : BalancingDispersionVanishes P (fun z => φ z.1) t O fun n ω => T n (W ω))
    (a : Bool) {m : 𝒳 → ℝ} (hm : Measurable m)
    (hres2 : Integrable (fun z : 𝒳 × Bool × ℝ => armIndObs a z * (z.2.2 - m z.1) ^ 2)
      (P.map (O 0)))
    (hreg : (P.map (O 0))[fun z => armIndObs a z * z.2.2 | MeasurableSpace.comap
      (fun z : 𝒳 × Bool × ℝ => (z.1, z.2.1)) inferInstance] =ᵐ[P.map (O 0)]
        fun z => armIndObs a z * m z.1) {σ2 : ℝ}
    (hvar : (P.map (O 0))[fun z => armIndObs a z * (z.2.2 - m z.1) ^ 2 | MeasurableSpace.comap
      (fun z : 𝒳 × Bool × ℝ => (z.1, z.2.1)) inferInstance] ≤ᵐ[P.map (O 0)] fun _ => σ2) :
    TendstoInMeasure P (fun n ω => ∑ i : Fin n,
      balancingWeights (fun j : Fin n => φ (O j ω).1 - T n (W ω)) i *
        (armIndObs a (O i ω) * ((O i ω).2.2 - m (O i ω).1))) atTop (fun _ => 0) := by
  obtain ⟨hmean, hvarR⟩ := armResidual_noise_moments a hm hres2 hreg hvar
  have he : Measurable fun z : 𝒳 × Bool × ℝ => armIndObs a z * (z.2.2 - m z.1) :=
    (measurable_armIndObs a).mul (measurable_snd.snd.sub (hm.comp measurable_fst))
  have he2 : Integrable (fun z : 𝒳 × Bool × ℝ => (armIndObs a z * (z.2.2 - m z.1)) ^ 2)
      (P.map (O 0)) := by
    simp_rw [armIndObs_mul_sq]; exact hres2
  have hD : TendstoInMeasure P (fun n ω => ∑ i : Fin n,
      balancingWeights (fun j : Fin n => φ (O j ω).1 - T n (W ω)) i ^ 2 * max σ2 0)
      atTop (fun _ => 0) := by
    have h := hdisp.const_mul (max σ2 0)
    simp only [mul_zero] at h
    refine h.of_norm_le (Eventually.of_forall fun n ω => ?_)
    rw [Real.norm_eq_abs, Real.norm_eq_abs, Finset.mul_sum]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ((Finset.sum_le_sum fun i _ => ?_).trans
      (le_abs_self _))
    rw [abs_of_nonneg (mul_nonneg (sq_nonneg _) (le_max_right _ _)), mul_left_comm]
    refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg _)
    nlinarith [le_max_right σ2 0, sq_nonneg ‖φ (O i ω).1 - t‖]
  exact tendstoInMeasure_weighted_noise_of_indepFun (O := O)
    (C := fun z : 𝒳 × Bool × ℝ => (z.1, z.2.1))
    (e := fun z => armIndObs a z * (z.2.2 - m z.1)) (v := fun _ => max σ2 0) (W := W)
    hO hOm hW hWO (measurable_fst.prodMk measurable_snd.fst) he he2 hmean
    measurable_const (fun _ => le_max_right _ _) (integrable_const _) hvarR
    (fun n i q' => balancingWeights (fun j : Fin n => φ (q'.1 j).1 - T n q'.2) i)
    (fun n i => measurable_balancingWeights_outside hφ measurable_fst hT n i)
    (fun n i _ => abs_balancingWeights_le_one _ i) hD

/-- **Consistency of the weighted arm mean under feasibility and vanishing dispersion.** Let `O`
be an i.i.d. sample of records `(X, A, Y)` with measurable coordinates, `W` data independent of
the sample and `tₙ = Tₙ(W)` measurable reported targets with `tₙ → t` in probability. Assume:
* feasibility with probability tending to one: the entropy balancing weights at `tₙ` form a
  probability vector balancing the features at `tₙ`;
* vanishing dispersion: `∑ᵢ cₙᵢ² (1 + ‖φ(Xᵢ) - t‖²) → 0` in probability;
* square integrable features, `E‖φ(X) - t‖² < ∞`;
* randomized assignment, `A` independent of `X`, with `P(A = a) > 0`;
* for arm `a` only: `E[1{A = a} Y | X, A] = 1{A = a} m(X)` with `m = a₀ + bᵀφ`, a square
  integrable residual on the arm, and `E[1{A = a}(Y - m(X))² | X, A] ≤ σ²`.
Then the weighted arm mean at the targets `tₙ` is consistent for `a₀ + bᵀt`. -/
theorem sampleBalancedArmMean_isConsistent_of_dispersion (hO : IsIIDSample O P)
    (hOm : ∀ i, Measurable (O i)) {φ : 𝒳 → Fin p → ℝ} (hφ : Measurable φ) {t : Fin p → ℝ}
    {W : Ω → 𝒲} (hW : Measurable W) (hWO : IndepFun W (fun ω k => O k ω) P)
    {T : ℕ → 𝒲 → Fin p → ℝ} (hT : ∀ n, Measurable (T n))
    (htm : TendstoInMeasure P (fun n ω => T n (W ω)) atTop (fun _ => t))
    (hfeas : WithProbTendingToOne P
      (balancingFeasibleEvent (fun z => φ z.1) O fun n ω => T n (W ω)))
    (hdisp : BalancingDispersionVanishes P (fun z => φ z.1) t O fun n ω => T n (W ω))
    (hφ2 : Integrable (fun z : 𝒳 × Bool × ℝ => ‖φ z.1 - t‖ ^ 2) (P.map (O 0)))
    (hind : IndepFun (fun z : 𝒳 × Bool × ℝ => z.1) (fun z => z.2.1) (P.map (O 0))) (a : Bool)
    (hq : 0 < (P.map (O 0)).real {z | z.2.1 = a}) {m : 𝒳 → ℝ}
    (hres2 : Integrable (fun z : 𝒳 × Bool × ℝ => armIndObs a z * (z.2.2 - m z.1) ^ 2)
      (P.map (O 0)))
    (hreg : (P.map (O 0))[fun z => armIndObs a z * z.2.2 | MeasurableSpace.comap
      (fun z : 𝒳 × Bool × ℝ => (z.1, z.2.1)) inferInstance] =ᵐ[P.map (O 0)]
        fun z => armIndObs a z * m z.1) {σ2 : ℝ}
    (hvar : (P.map (O 0))[fun z => armIndObs a z * (z.2.2 - m z.1) ^ 2 | MeasurableSpace.comap
      (fun z : 𝒳 × Bool × ℝ => (z.1, z.2.1)) inferInstance] ≤ᵐ[P.map (O 0)] fun _ => σ2)
    {a0 : ℝ} {b : Fin p → ℝ} (haff : ∀ x, m x = a0 + b ⬝ᵥ φ x) :
    IsConsistent (fun n ω => sampleBalancedArmMean φ (T n (W ω)) O a n ω) (a0 + b ⬝ᵥ t) P := by
  have hm : Measurable m := by
    rw [show m = fun x => a0 + b ⬝ᵥ φ x from funext haff]
    exact measurable_const.add ((continuous_const.dotProduct continuous_id).measurable.comp hφ)
  have hN1 := tendstoInMeasure_balanced_alloc_noise hO hOm hφ hW hWO hT hdisp hφ2 hind a
    (ψ := fun _ => (1 : ℝ)) (K := 1) measurable_const fun x => by
      nlinarith [sq_nonneg ‖φ x - t‖]
  have hN2 := tendstoInMeasure_balanced_alloc_noise hO hOm hφ hW hWO hT hdisp hφ2 hind a hm
    (K := 2 * (a0 + b ⬝ᵥ t) ^ 2 + 2 * (p * ‖b‖) ^ 2) fun x => by
      rw [haff]; exact sq_affine_features_le φ t a0 b x
  have hN3 := tendstoInMeasure_balanced_residual_noise hO hOm hφ hW hWO hT hdisp a hm hres2
    hreg hvar
  set q := (P.map (O 0)).real {z : 𝒳 × Bool × ℝ | z.2.1 = a} with hqdef
  set G : ℝ × ℝ × ℝ × (Fin p → ℝ) → ℝ := fun u =>
    (q * (a0 + b ⬝ᵥ u.2.2.2) + u.2.1 + u.2.2.1) / (q + u.1) with hG
  have hGc : ContinuousAt G (0, 0, 0, t) := by
    refine ContinuousAt.div (by fun_prop) (by fun_prop) ?_
    simpa using hq.ne'
  have h34 := hN3.prodMk htm
  have h234 := hN2.prodMk h34
  have h1234 := hN1.prodMk h234
  have hlim := TendstoInMeasure.comp_continuousAt (g := G) h1234 hGc
  have hG0 : G (0, 0, 0, t) = a0 + b ⬝ᵥ t := by
    simp only [hG, add_zero]; field_simp
  rw [hG0] at hlim
  refine hlim.congr_withProbTendingToOne hfeas fun n ω hc => ?_
  have hdec := weightedArmMean_eq_noise_decomp (z := fun i : Fin n => O i ω) (t := T n (W ω))
    hc a (mu := fun _ => m) haff q
  rw [sampleBalancedArmMean, hdec]

/-- Square integrability of the features from an exponential moment of order at least one. -/
theorem integrable_sq_norm_of_integrable_exp {𝒟 : Type*} [MeasurableSpace 𝒟] {ν : Measure 𝒟}
    {g : 𝒟 → ℝ} (hg : Measurable g) (hg0 : ∀ z, 0 ≤ g z) {κ : ℝ} (hκ : 1 ≤ κ)
    (hexp : Integrable (fun z => Real.exp (κ * g z)) ν) : Integrable (fun z => g z ^ 2) ν :=
  (hexp.const_mul 2).mono' (hg.pow_const 2).aestronglyMeasurable (ae_of_all _ fun z => by
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    have h1 := one_add_sq_le_two_mul_exp_of_nonneg (hg0 z)
    have h2 : Real.exp (g z) ≤ Real.exp (κ * g z) :=
      Real.exp_le_exp.2 (le_mul_of_one_le_left (hg0 z) hκ)
    nlinarith)

/-- **Random targets and unbounded features.** Under the margin condition at `t` with margin `δ`
for the law of the features `φ(X)`, a finite exponential moment
`E[exp(κ ‖φ(X) - t‖)] < ∞` of order `κ = 2 p (16 / δ²) + 1`, reported targets `tₙ = Tₙ(W)`
computed from data `W` independent of the sample with `tₙ → t` in probability, randomized
assignment and the arm `a` hypotheses of `sampleBalancedArmMean_isConsistent_of_dispersion`, the
weighted arm mean at `tₙ` is consistent for `a₀ + bᵀt`. -/
theorem sampleBalancedArmMean_isConsistent_of_integrable_exp (hO : IsIIDSample O P)
    (hOm : ∀ i, Measurable (O i)) {φ : 𝒳 → Fin p → ℝ} (hφ : Measurable φ) {t : Fin p → ℝ}
    {δ : ℝ} (hδ : 0 < δ)
    (hmargin : ∀ v : Fin p → ℝ, ‖v‖ = 1 →
      δ ≤ (P.map (O 0)).real {z | δ ≤ v ⬝ᵥ (φ z.1 - t)})
    (hexp : Integrable (fun z : 𝒳 × Bool × ℝ =>
      Real.exp ((2 * p * (16 / δ ^ 2) + 1) * ‖φ z.1 - t‖)) (P.map (O 0)))
    {W : Ω → 𝒲} (hW : Measurable W) (hWO : IndepFun W (fun ω k => O k ω) P)
    {T : ℕ → 𝒲 → Fin p → ℝ} (hT : ∀ n, Measurable (T n))
    (htm : TendstoInMeasure P (fun n ω => T n (W ω)) atTop (fun _ => t))
    (hind : IndepFun (fun z : 𝒳 × Bool × ℝ => z.1) (fun z => z.2.1) (P.map (O 0))) (a : Bool)
    (hq : 0 < (P.map (O 0)).real {z | z.2.1 = a}) {m : 𝒳 → ℝ}
    (hres2 : Integrable (fun z : 𝒳 × Bool × ℝ => armIndObs a z * (z.2.2 - m z.1) ^ 2)
      (P.map (O 0)))
    (hreg : (P.map (O 0))[fun z => armIndObs a z * z.2.2 | MeasurableSpace.comap
      (fun z : 𝒳 × Bool × ℝ => (z.1, z.2.1)) inferInstance] =ᵐ[P.map (O 0)]
        fun z => armIndObs a z * m z.1) {σ2 : ℝ}
    (hvar : (P.map (O 0))[fun z => armIndObs a z * (z.2.2 - m z.1) ^ 2 | MeasurableSpace.comap
      (fun z : 𝒳 × Bool × ℝ => (z.1, z.2.1)) inferInstance] ≤ᵐ[P.map (O 0)] fun _ => σ2)
    {a0 : ℝ} {b : Fin p → ℝ} (haff : ∀ x, m x = a0 + b ⬝ᵥ φ x) :
    IsConsistent (fun n ω => sampleBalancedArmMean φ (T n (W ω)) O a n ω) (a0 + b ⬝ᵥ t) P := by
  have hf : Measurable fun z : 𝒳 × Bool × ℝ => φ z.1 := hφ.comp measurable_fst
  have htm' : TendstoInMeasure P (fun n ω => T n (W ω)) atTop (fun _ => t) := htm
  have hfeas : WithProbTendingToOne P
      (balancingFeasibleEvent (fun z => φ z.1) O fun n ω => T n (W ω)) :=
    (withProbTendingToOne_balancingFeasible hO hf hδ hmargin htm').mono fun n ω hω => by
      obtain ⟨-, -, β, -, -, hmem, -⟩ := hω
      exact hmem
  have hdisp := balancingDispersionVanishes_of_integrable_exp hO hOm hf hδ hmargin htm' hexp
  have hφ2 : Integrable (fun z : 𝒳 × Bool × ℝ => ‖φ z.1 - t‖ ^ 2) (P.map (O 0)) :=
    integrable_sq_norm_of_integrable_exp (g := fun z : 𝒳 × Bool × ℝ => ‖φ z.1 - t‖)
      (hf.sub_const t).norm (fun _ => norm_nonneg _)
      (le_add_of_nonneg_left (by positivity)) hexp
  exact sampleBalancedArmMean_isConsistent_of_dispersion hO hOm hφ hW hWO hT htm hfeas hdisp
    hφ2 hind a hq hres2 hreg hvar haff

/-- **The interior condition with all exponential moments.** If `t` lies in the interior of the
closed convex hull of the support of the law of `φ(X)` and `E[exp(κ ‖φ(X) - t‖)] < ∞` for every
`κ`, the weighted arm mean at reported targets `tₙ = Tₙ(W) → t` (random, independent of the
sample) is consistent for `a₀ + bᵀt`. The margin, hence the order of the moment actually used,
is not explicit under the interior condition, which is why all orders are assumed. -/
theorem sampleBalancedArmMean_isConsistent_of_interior_of_integrable_exp (hO : IsIIDSample O P)
    (hOm : ∀ i, Measurable (O i)) {φ : 𝒳 → Fin p → ℝ} (hφ : Measurable φ) {t : Fin p → ℝ}
    (hint : t ∈ interior (closedConvexHull ℝ ((P.map (O 0)).map fun z => φ z.1).support))
    (hexp : ∀ κ : ℝ, Integrable (fun z : 𝒳 × Bool × ℝ => Real.exp (κ * ‖φ z.1 - t‖))
      (P.map (O 0)))
    {W : Ω → 𝒲} (hW : Measurable W) (hWO : IndepFun W (fun ω k => O k ω) P)
    {T : ℕ → 𝒲 → Fin p → ℝ} (hT : ∀ n, Measurable (T n))
    (htm : TendstoInMeasure P (fun n ω => T n (W ω)) atTop (fun _ => t))
    (hind : IndepFun (fun z : 𝒳 × Bool × ℝ => z.1) (fun z => z.2.1) (P.map (O 0))) (a : Bool)
    (hq : 0 < (P.map (O 0)).real {z | z.2.1 = a}) {m : 𝒳 → ℝ}
    (hres2 : Integrable (fun z : 𝒳 × Bool × ℝ => armIndObs a z * (z.2.2 - m z.1) ^ 2)
      (P.map (O 0)))
    (hreg : (P.map (O 0))[fun z => armIndObs a z * z.2.2 | MeasurableSpace.comap
      (fun z : 𝒳 × Bool × ℝ => (z.1, z.2.1)) inferInstance] =ᵐ[P.map (O 0)]
        fun z => armIndObs a z * m z.1) {σ2 : ℝ}
    (hvar : (P.map (O 0))[fun z => armIndObs a z * (z.2.2 - m z.1) ^ 2 | MeasurableSpace.comap
      (fun z : 𝒳 × Bool × ℝ => (z.1, z.2.1)) inferInstance] ≤ᵐ[P.map (O 0)] fun _ => σ2)
    {a0 : ℝ} {b : Fin p → ℝ} (haff : ∀ x, m x = a0 + b ⬝ᵥ φ x) :
    IsConsistent (fun n ω => sampleBalancedArmMean φ (T n (W ω)) O a n ω) (a0 + b ⬝ᵥ t) P := by
  obtain ⟨δ, hδ, hmargin⟩ := exists_margin_of_mem_interior_map (hφ.comp measurable_fst) hint
  exact sampleBalancedArmMean_isConsistent_of_integrable_exp hO hOm hφ hδ hmargin (hexp _) hW hWO
    hT htm hind a hq hres2 hreg hvar haff

/-- **Deterministic converging targets and features bounded almost surely.** For reported
targets `tₙ → t` (deterministic), features with `‖φ(X) - t‖ ≤ B` almost surely, the interior
condition at `t`, randomized assignment and the arm `a` hypotheses, the weighted arm mean at
`tₙ` is consistent for `a₀ + bᵀt`. -/
theorem sampleBalancedArmMean_isConsistent_of_tendsto (hO : IsIIDSample O P)
    (hOm : ∀ i, Measurable (O i)) {φ : 𝒳 → Fin p → ℝ} (hφ : Measurable φ) {t : Fin p → ℝ}
    (hint : t ∈ interior (closedConvexHull ℝ ((P.map (O 0)).map fun z => φ z.1).support))
    {B : ℝ} (hB : ∀ᵐ z ∂(P.map (O 0)), ‖φ z.1 - t‖ ≤ B)
    {tn : ℕ → Fin p → ℝ} (htn : Tendsto tn atTop (𝓝 t))
    (hind : IndepFun (fun z : 𝒳 × Bool × ℝ => z.1) (fun z => z.2.1) (P.map (O 0))) (a : Bool)
    (hq : 0 < (P.map (O 0)).real {z | z.2.1 = a}) {m : 𝒳 → ℝ}
    (hres2 : Integrable (fun z : 𝒳 × Bool × ℝ => armIndObs a z * (z.2.2 - m z.1) ^ 2)
      (P.map (O 0)))
    (hreg : (P.map (O 0))[fun z => armIndObs a z * z.2.2 | MeasurableSpace.comap
      (fun z : 𝒳 × Bool × ℝ => (z.1, z.2.1)) inferInstance] =ᵐ[P.map (O 0)]
        fun z => armIndObs a z * m z.1) {σ2 : ℝ}
    (hvar : (P.map (O 0))[fun z => armIndObs a z * (z.2.2 - m z.1) ^ 2 | MeasurableSpace.comap
      (fun z : 𝒳 × Bool × ℝ => (z.1, z.2.1)) inferInstance] ≤ᵐ[P.map (O 0)] fun _ => σ2)
    {a0 : ℝ} {b : Fin p → ℝ} (haff : ∀ x, m x = a0 + b ⬝ᵥ φ x) :
    IsConsistent (fun n ω => sampleBalancedArmMean φ (tn n) O a n ω) (a0 + b ⬝ᵥ t) P := by
  have hexp : ∀ κ : ℝ, Integrable (fun z : 𝒳 × Bool × ℝ => Real.exp (κ * ‖φ z.1 - t‖))
      (P.map (O 0)) := fun κ =>
    (integrable_const (Real.exp (|κ| * B))).mono'
      (Real.measurable_exp.comp (measurable_const.mul
        ((hφ.comp measurable_fst).sub_const t).norm)).aestronglyMeasurable
      (hB.mono fun z hz => by
        rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
        refine Real.exp_le_exp.2 ((le_abs_self κ |> fun h =>
          mul_le_mul_of_nonneg_right h (norm_nonneg _)).trans ?_)
        exact mul_le_mul_of_nonneg_left hz (abs_nonneg κ))
  have htm : TendstoInMeasure P (fun n (_ : Ω) => (fun n (_ : Unit) => tn n) n ()) atTop
      (fun _ => t) :=
    tendstoInMeasure_of_tendsto_ae (fun _ => aestronglyMeasurable_const)
      (ae_of_all _ fun _ => htn)
  exact sampleBalancedArmMean_isConsistent_of_interior_of_integrable_exp hO hOm hφ hint hexp
    (W := fun _ => ()) measurable_const (indepFun_const_left () _) (T := fun n _ => tn n)
    (fun _ => measurable_const) htm hind a hq hres2 hreg hvar haff

end PopulationAdjustment

end CausalInference
