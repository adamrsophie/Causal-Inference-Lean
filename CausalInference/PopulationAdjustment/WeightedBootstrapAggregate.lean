/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.PopulationAdjustment.WeightedBootstrapExamplesMatched
public import CausalInference.PopulationAdjustment.WeightedNormalityWaldTwoSample

/-!
# The bootstrap with an estimated aggregate

The unanchored comparison `c₀ - m₀` is estimated by `Ĉₙ - m̂ₙ`, where the aggregate mean `Ĉₙ`
is itself an estimate, independent of the individual records, with
`√n (Ĉₙ - c₀) → N(0, τ²)`. The interval that resamples only the individual records and holds
`Ĉₙ` fixed is `[Ĉₙ - q*(1 - α/2), Ĉₙ - q*(α/2)]`, with `q*` the quantiles of the bootstrap law
of the weighted arm mean; it contains `c₀ - m₀` exactly when
`Ĉₙ - (c₀ - m₀) ∈ [q*(α/2), q*(1 - α/2)]`.

Its coverage tends to `F(√σ² z) - F(-√σ² z)`, `F` the distribution function of
`N(0, σ² + τ²)` (`tendsto_bootstrapUnanchored_estimatedAggregate_coverage`): the bootstrap law
carries the variance `σ²` of the records only, while `√n ((Ĉₙ - m̂ₙ) - (c₀ - m₀))` has the
variance `σ² + τ²`. For `τ² > 0` this limit is strictly below `1 - α`
(`cdf_sub_cdf_neg_lt_one_sub`).

In the two coin model with one matched feature and an independent sample of fair coins for the
aggregate, `σ² = 1` and `τ² = 1/4`: the coverage tends to `F(z) - F(-z)` for `F` the
distribution function of `N(0, 5/4)`, which is strictly below `1 - α`
(`example_bootstrapUnanchored_estimatedAggregate_coverage`).

## Main results

* `cdf_sub_cdf_neg_lt_one_sub`: the undercoverage of a too narrow normal interval.
* `tendsto_bootstrapUnanchored_estimatedAggregate_coverage`: the limit of the coverage.
* `example_bootstrapUnanchored_estimatedAggregate_coverage`,
  `example_estimatedAggregate_coverage_lt`: the numeric instance.

## References

* B. Efron (1979), *Bootstrap methods: another look at the jackknife*, Annals of Statistics 7.
* J. E. Signorovitch and coauthors, PharmacoEconomics 28 (2010).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Finset Matrix Set
open scoped Topology ENNReal NNReal

namespace CausalInference

namespace PopulationAdjustment

open PointTreatment Bootstrap IndirectComparison PosteriorLimit

/-- **A too narrow normal interval undercovers**: for `0 < σ² < v`, `α ∈ (0, 1)` and
`Φ(z) = 1 - α/2`, the probability `F(√σ² z) - F(-√σ² z)` of `[-√σ² z, √σ² z]` under
`N(0, v)` is strictly below `1 - α`. -/
theorem cdf_sub_cdf_neg_lt_one_sub {σ2 v : ℝ} (hσ : 0 < σ2) (hv : σ2 < v) {α z : ℝ}
    (hα : α ∈ Ioo (0 : ℝ) 1) (hz : cdf (gaussianReal 0 1) z = 1 - α / 2) :
    cdf (gaussianReal 0 v.toNNReal) (√σ2 * z) - cdf (gaussianReal 0 v.toNNReal) (-(√σ2 * z)) <
      1 - α := by
  have hv0 : 0 < v := hσ.trans hv
  have hz0 : 0 < z := pos_of_cdf_eq hα hz
  have hlt : √σ2 * z < √v * z :=
    mul_lt_mul_of_pos_right (Real.sqrt_lt_sqrt hσ.le hv) hz0
  have hmono := cdf_gaussianReal_strictMono 0 (v := v.toNNReal) (by simpa using hv0)
  have h1 := hmono hlt
  have h2 := hmono (neg_lt_neg hlt)
  rw [← cdf_sub_cdf_neg_eq hv0 hz]
  linarith

variable {𝒳 : Type*} {p : ℕ} [MeasurableSpace 𝒳] {Ω : Type*} [MeasurableSpace Ω]
  {P : Measure Ω} {O : ℕ → Ω → 𝒳 × Bool × ℝ}

/-- **Coverage of the bootstrap interval with an estimated aggregate.** Under the hypotheses of
the asymptotic normality theorem for the arm `true` with `σ² > 0`, an aggregate estimate `Ĉₙ`
independent of the first `n` records with `√n (Ĉₙ - c₀) → N(0, τ²)`, `τ² ≥ 0`, the interval
`[Ĉₙ - q*(1 - α/2), Ĉₙ - q*(α/2)]` that resamples only the records contains `c₀ - m₀` with
probability tending to `F(√σ² z) - F(-√σ² z)`, `F` the distribution function of
`N(0, σ² + τ²)`. -/
theorem tendsto_bootstrapUnanchored_estimatedAggregate_coverage [IsProbabilityMeasure P]
    (hO : IsIIDSample O P) {φ : 𝒳 → Fin p → ℝ} (hφ : Measurable φ) {t : Fin p → ℝ} {B : ℝ}
    (hB : ∀ x, ‖φ x - t‖ ≤ B) {δ : ℝ} (hδ : 0 < δ) (hmargin : ∀ v : Fin p → ℝ, ‖v‖ = 1 →
      δ ≤ (P.map (O 0)).real {z | δ ≤ v ⬝ᵥ (φ z.1 - t)})
    (hq : 0 < (P.map (O 0)).real {z | z.2.1 = true})
    (hy : MemLp (fun z : 𝒳 × Bool × ℝ => z.2.2) 2 (P.map (O 0)))
    (hσ : 0 < weightedArmVariance (P.map (O 0)) φ t true)
    {C : ℕ → Ω → ℝ} {c₀ τ2 : ℝ} (hτ : 0 ≤ τ2)
    (hindep : ∀ n, IndepFun (fun ω (i : Fin n) => O i ω) (C n) P)
    (hC : TendstoInDistribution (fun (n : ℕ) ω => √(n : ℝ) * (C n ω - c₀)) atTop id
      (fun _ => P) (gaussianReal 0 τ2.toNNReal))
    {α z : ℝ} (hα : α ∈ Ioo (0 : ℝ) 1) (hz : cdf (gaussianReal 0 1) z = 1 - α / 2) :
    Tendsto (fun n => P.real {ω | C n ω - (c₀ -
        tiltArmMean (P.map (O 0)) φ t true (tiltMinimizer (P.map (O 0)) φ t)) ∈
          percentileInterval (bootstrapLaw (bootstrapArmMean φ t true) O n ω) α}) atTop
      (𝓝 (cdf (gaussianReal 0 (weightedArmVariance (P.map (O 0)) φ t true + τ2).toNNReal)
          (√(weightedArmVariance (P.map (O 0)) φ t true) * z) -
        cdf (gaussianReal 0 (weightedArmVariance (P.map (O 0)) φ t true + τ2).toNNReal)
          (-(√(weightedArmVariance (P.map (O 0)) φ t true) * z)))) := by
  set σ2 := weightedArmVariance (P.map (O 0)) φ t true with hσ2
  set m₀ := tiltArmMean (P.map (O 0)) φ t true (tiltMinimizer (P.map (O 0)) φ t) with hm₀
  have hAL := sampleBalancedArmMean_isAsymptoticallyLinear hO hφ hB hδ hmargin true hq hy
  have hBvM := bootstrapArmMean_isBernsteinVonMisesWeak hO hφ hB hδ hmargin true hq hy
  obtain ⟨hhi, hlo⟩ := hBvM.tendstoInMeasure_credibleInterval_endpoints hσ hz
  have hc : 0 < √σ2 * z := mul_pos (Real.sqrt_pos.2 hσ) (pos_of_cdf_eq hα hz)
  -- the limit of the data part
  have hmeas : ∀ n, AEMeasurable (fun ω => sampleBalancedArmMean φ t O true n ω) P := fun n =>
    (measurable_bootstrapArmMean hφ t true n).comp_aemeasurable
      (AEMeasurable.of_eval fun i => hO.aemeasurable i)
  have hvar : P[fun ω => weightedArmInfluence (P.map (O 0)) φ t true (O 0 ω) ^ 2] = σ2 := by
    rw [integral_sq_comp_eq hO hAL.measurable]; rfl
  have hX := hAL.tendstoInDistribution hO hmeas (show HasLaw (id : ℝ → ℝ) (gaussianReal 0
    (P[fun ω => weightedArmInfluence (P.map (O 0)) φ t true (O 0 ω) ^ 2]).toNNReal)
    (gaussianReal 0 σ2.toNNReal) by rw [hvar]; exact HasLaw.id)
  have hZ := hX.continuous_comp continuous_neg
  have hlawZ : HasLaw ((fun x : ℝ => -x) ∘ id) (gaussianReal 0 σ2.toNNReal)
      (gaussianReal 0 σ2.toNNReal) := by
    have := gaussianReal_neg (HasLaw.id (μ := gaussianReal 0 σ2.toNNReal))
    rw [neg_zero] at this
    exact this
  have hind : ∀ n : ℕ, IndepFun (fun ω => √(n : ℝ) * (C n ω - c₀))
      ((fun x : ℝ => -x) ∘ fun ω => √(n : ℝ) * (sampleBalancedArmMean φ t O true n ω - m₀)) P :=
    fun n => (hindep n).symm.comp (φ := fun c => √(n : ℝ) * (c - c₀))
      (ψ := fun x => -(√(n : ℝ) * (bootstrapArmMean φ t true n x - m₀)))
      (measurable_const.mul (measurable_id.sub_const _))
      (((measurable_bootstrapArmMean hφ t true n).sub_const _).const_mul _).neg
  have hsum := tendstoInDistribution_add_of_indepFun hC hZ hind HasLaw.id hlawZ
    (HasLaw.id (μ := gaussianReal 0 (τ2.toNNReal + σ2.toNNReal)))
  have hv : (σ2 + τ2).toNNReal = τ2.toNNReal + σ2.toNNReal := by
    rw [Real.toNNReal_add hσ.le hτ, add_comm]
  have hY : HasLaw (id : ℝ → ℝ) (gaussianReal 0 (σ2 + τ2).toNNReal)
      (gaussianReal 0 (τ2.toNNReal + σ2.toNNReal)) := by
    rw [hv]; exact HasLaw.id
  refine tendsto_measureReal_squeeze (by linarith) hY hsum hc hlo hhi
    (R := fun n ω => √(n : ℝ) * (C n ω - c₀) + -(√(n : ℝ) *
      (sampleBalancedArmMean φ t O true n ω - m₀))) (fun n ω => rfl) ?_
  filter_upwards [eventually_ge_atTop 1] with n hn ω
  have hsq : 0 < √(n : ℝ) := Real.sqrt_pos.2 (by exact_mod_cast hn)
  simp only [percentileInterval, Set.mem_Icc]
  rw [show √(n : ℝ) * (C n ω - c₀) + -(√(n : ℝ) * (sampleBalancedArmMean φ t O true n ω - m₀)) =
      √(n : ℝ) * (C n ω - (c₀ - m₀) - sampleBalancedArmMean φ t O true n ω) by ring,
    mul_le_mul_iff_right₀ hsq, mul_le_mul_iff_right₀ hsq]
  constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith

/-! ### The two coin model with an aggregate from fair coins -/

section Example

variable {Ω₁ Ω₂ : Type*} [MeasurableSpace Ω₁] [MeasurableSpace Ω₂]
  {P₁ : Measure Ω₁} {P₂ : Measure Ω₂} [IsProbabilityMeasure P₁] [IsProbabilityMeasure P₂]
  {O : ℕ → Ω₁ → Bool × Bool × ℝ} {Bc : ℕ → Ω₂ → Bool}

/-- **The estimated aggregate in the two coin model.** The records are an i.i.d. sample of the
two coin record law, and the aggregate mean is the sample mean `B̄ₙ` of an independent i.i.d.
sample of fair coins (`c₀ = 1/2`, `τ² = 1/4`). The interval that resamples only the records
contains `1/2 - 2` with probability tending to `F(z) - F(-z)`, `F` the distribution function of
`N(0, 5/4)`. -/
theorem example_bootstrapUnanchored_estimatedAggregate_coverage (hOm : ∀ i, Measurable (O i))
    (hO : IsIIDSample O P₁) (hlaw : P₁.map (O 0) = exampleRecordLaw)
    (hBm : ∀ i, Measurable (Bc i)) (hB : IsIIDSample Bc P₂)
    (hlawB : P₂.map (Bc 0) = EffectMeasure.halfLaw)
    {α z : ℝ} (hα : α ∈ Ioo (0 : ℝ) 1) (hz : cdf (gaussianReal 0 1) z = 1 - α / 2) :
    Tendsto (fun n => (P₁.prod P₂).real {ω |
        sampleMean coinVal (fun i (ω : Ω₁ × Ω₂) => Bc i ω.2) n ω - (1 / 2 - 2) ∈
          percentileInterval (bootstrapLaw (bootstrapArmMean exampleFeature exampleTarget true)
            (fun i (ω : Ω₁ × Ω₂) => O i ω.1) n ω) α}) atTop
      (𝓝 (cdf (gaussianReal 0 (5 / 4 : ℝ).toNNReal) z -
        cdf (gaussianReal 0 (5 / 4 : ℝ).toNNReal) (-z))) := by
  have hO' := isIIDSample_comp_fst_prod (P₂ := P₂) hOm hO
  have hlaw' : (P₁.prod P₂).map (fun ω : Ω₁ × Ω₂ => O 0 ω.1) = exampleRecordLaw := by
    rw [map_comp_fst_prod hOm, hlaw]
  have h := tendsto_bootstrapUnanchored_estimatedAggregate_coverage hO'
    measurable_exampleFeature example_bound (by norm_num : (0 : ℝ) < 1 / 2)
    (by rw [hlaw']; exact example_margin) (by rw [hlaw', example_prob_arm]; norm_num)
    (by rw [hlaw']; exact example_memLp_outcome)
    (by rw [hlaw', example_weightedArmVariance_true]; norm_num)
    (C := sampleMean coinVal (fun i (ω : Ω₁ × Ω₂) => Bc i ω.2)) (c₀ := 1 / 2)
    (τ2 := 1 / 4) (by norm_num)
    (fun n => indepFun_comp_fst_comp_snd (F := fun ω (i : Fin n) => O i ω)
      (measurable_pi_iff.2 fun i => hOm i) (measurable_sampleMean_coinVal hBm n))
    (coin_sampleMean_tendstoInDistribution hBm hB hlawB) hα hz
  rw [hlaw', example_weightedArmVariance_true, example_tiltArmMean_true] at h
  rw [show (1 : ℝ) + 1 / 4 = 5 / 4 by norm_num, Real.sqrt_one, one_mul] at h
  exact h

/-- **The undercoverage in the two coin model**: `F(z) - F(-z) < 1 - α` for `F` the distribution
function of `N(0, 5/4)`. -/
theorem example_estimatedAggregate_coverage_lt {α z : ℝ} (hα : α ∈ Ioo (0 : ℝ) 1)
    (hz : cdf (gaussianReal 0 1) z = 1 - α / 2) :
    cdf (gaussianReal 0 (5 / 4 : ℝ).toNNReal) z -
      cdf (gaussianReal 0 (5 / 4 : ℝ).toNNReal) (-z) < 1 - α := by
  have h := cdf_sub_cdf_neg_lt_one_sub (σ2 := 1) (v := 5 / 4) one_pos (by norm_num) hα hz
  simpa using h

end Example

end PopulationAdjustment

end CausalInference
