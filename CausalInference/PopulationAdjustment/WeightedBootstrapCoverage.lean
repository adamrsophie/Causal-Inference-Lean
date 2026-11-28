/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.PopulationAdjustment.WeightedBootstrapLinearization
public import CausalInference.PopulationAdjustment.WeightedNormalityContrast
public import CausalInference.Estimation.DeltaMethodMultivariate

/-!
# Coverage of the bootstrap intervals for the weighted arm mean and the comparisons

For a level `α ∈ (0, 1)` the bootstrap percentile interval is
`[q*(α/2), q*(1 - α/2)]` and the basic interval is `[2 T̂ₙ - q*(1 - α/2), 2 T̂ₙ - q*(α/2)]`,
where `q*` are the quantiles of the bootstrap law of `T*ₙ` given the data.

* `IsBootstrapLinear.tendsto_coverage`: if the data estimate `T̂ₙ` is asymptotically linear at
  `θ` with influence function `ψ`, the statistic is bootstrap linear with the same `ψ`, and
  `E ψ(O_0)² > 0`, both intervals cover `θ` with probability tending to `1 - α`.
* `tendsto_bootstrapArmMean_coverage`: the weighted arm mean, centered at
  `m₀ = tiltArmMean`, the weighted mean of the arm under the population tilt.
* `tendsto_bootstrapIndexContrast_coverage`: the anchored comparison on the identity scale,
  `(m̂_false - m̂_true) - d` for a constant aggregate comparison `d` of the other trial.
* `tendsto_bootstrapUnanchored_coverage`: the unanchored comparison `c - m̂_true` on the
  identity scale for a constant aggregate mean `c`.

The arm mean statements assume only the model primitives of the asymptotic normality theorem and
a positive variance: bootstrap linearity of the arm means is `isBootstrapLinear_bootstrapArmMean`.
The aggregate quantities `d` and `c` are constants: they are not resampled.

`bootstrapArmMean_eq_of_affine` is a deterministic identity: if a sample admits positive
balancing weights, has a record in arm `a`, and `1{aᵢ = a} (yᵢ - m) = γᵀ (φ(xᵢ) - t)` for every
record, its weighted arm mean is `m`.

## Main results

* `IsBootstrapLinear.sub`, `IsBootstrapLinear.const`.
* `IsBootstrapLinear.tendsto_coverage`, `tendsto_bootstrapArmMean_coverage`,
  `tendsto_bootstrapIndexContrast_coverage`, `tendsto_bootstrapUnanchored_coverage`.
* `bootstrapArmMean_eq_of_affine`.

## References

* B. Efron (1979), *Bootstrap methods: another look at the jackknife*, Annals of Statistics 7.
* A. W. van der Vaart (1998), *Asymptotic Statistics*, Cambridge University Press, chapter 23.
* J. E. Signorovitch and coauthors, PharmacoEconomics 28 (2010).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Finset Matrix Set
open scoped Topology ENNReal

namespace CausalInference

namespace PopulationAdjustment

open PointTreatment Bootstrap PosteriorLimit

section General

variable {Ω 𝒪 : Type*} {mΩ : MeasurableSpace Ω} [MeasurableSpace 𝒪] {P : Measure Ω}
  {O : ℕ → Ω → 𝒪}

/-- **Differences of bootstrap linear statistics** are bootstrap linear. -/
theorem IsBootstrapLinear.sub {T₁ T₂ : (n : ℕ) → (Fin n → 𝒪) → ℝ} {ψ₁ ψ₂ : 𝒪 → ℝ}
    (h₁ : IsBootstrapLinear P O T₁ ψ₁) (h₂ : IsBootstrapLinear P O T₂ ψ₂) :
    IsBootstrapLinear P O (fun n y => T₁ n y - T₂ n y) (fun z => ψ₁ z - ψ₂ z) := by
  have h := h₁.linearCombination h₂ 1 (-1)
  have e1 : (fun n (y : Fin n → 𝒪) => 1 * T₁ n y + -1 * T₂ n y) =
      fun n y => T₁ n y - T₂ n y := by funext n y; ring
  have e2 : (fun z => 1 * ψ₁ z + -1 * ψ₂ z) = fun z => ψ₁ z - ψ₂ z := by funext z; ring
  rwa [e1, e2] at h

/-- **A constant statistic** is bootstrap linear with influence function `0`. -/
theorem IsBootstrapLinear.const (P : Measure Ω) (O : ℕ → Ω → 𝒪) (c : ℝ) :
    IsBootstrapLinear P O (fun _ _ => c) (fun _ => 0) := by
  intro ρ hρ
  have e : (fun (n : ℕ) (ω : Ω) => (resampleLaw O n ω).real
      {y | ρ ≤ |bootstrapRemainder (fun _ _ => c) (fun _ => 0) O n ω y|}) = fun _ _ => 0 := by
    funext n ω
    have : {y : Fin n → 𝒪 | ρ ≤ |bootstrapRemainder (fun _ _ => c) (fun _ => 0) O n ω y|} =
        ∅ := by
      ext y
      simp [bootstrapRemainder, resampleMean, sampleMean, not_le.2 hρ]
    rw [this, measureReal_empty]
  rw [e]
  exact tendstoInMeasure_const 0

/-- **Coverage of the bootstrap intervals for a bootstrap linear statistic.** Let `O` be an
i.i.d. sample under a probability measure and `T` a measurable statistic whose data estimate
`T̂ₙ` is asymptotically linear at `θ` with influence function `ψ`. If `T` is bootstrap linear
with the same `ψ` and `E ψ(O_0)² > 0`, then for `α ∈ (0, 1)` and `Φ(z) = 1 - α/2` the bootstrap
percentile and basic intervals cover `θ` with probability tending to `1 - α`. -/
theorem IsBootstrapLinear.tendsto_coverage [IsProbabilityMeasure P] (hO : IsIIDSample O P)
    {T : (n : ℕ) → (Fin n → 𝒪) → ℝ} (hT : ∀ n, Measurable (T n)) {θ : ℝ} {ψ : 𝒪 → ℝ}
    (hAL : IsAsymptoticallyLinear (fun n ω => T n (dataPrefix O n ω)) θ ψ O P)
    (hlin : IsBootstrapLinear P O T ψ) (hσ : 0 < P[fun ω => ψ (O 0 ω) ^ 2]) {α z : ℝ}
    (hα : α ∈ Ioo (0 : ℝ) 1) (hz : cdf (gaussianReal 0 1) z = 1 - α / 2) :
    Tendsto (fun n => P.real {ω | θ ∈ percentileInterval (bootstrapLaw T O n ω) α}) atTop
        (𝓝 (1 - α)) ∧
      Tendsto (fun n => P.real {ω | θ ∈ basicInterval (bootstrapLaw T O n ω)
        (T n (dataPrefix O n ω)) α}) atTop (𝓝 (1 - α)) := by
  have hvar : Var[fun ω => ψ (O 0 ω); P] = P[fun ω => ψ (O 0 ω) ^ 2] :=
    variance_of_integral_eq_zero hAL.memLp.aemeasurable hAL.integral_eq_zero
  have hB := hlin.isBernsteinVonMisesWeak hO hT hAL.measurable hAL.memLp
  rw [hvar] at hB
  have hmeas : ∀ n, AEMeasurable (fun ω => T n (dataPrefix O n ω)) P := fun n =>
    (hT n).comp_aemeasurable (AEMeasurable.of_eval fun i => hO.aemeasurable i)
  have hY := HasLaw.id (μ := gaussianReal 0 (P[fun ω => ψ (O 0 ω) ^ 2]).toNNReal)
  have hS := hAL.tendstoInDistribution hO hmeas hY
  exact ⟨tendsto_percentileInterval_coverage hσ hB hY hS hα hz,
    tendsto_basicInterval_coverage hσ hB hY hS hα hz⟩

end General

variable {𝒳 : Type*} {p : ℕ} [MeasurableSpace 𝒳] {Ω : Type*} [MeasurableSpace Ω]
  {P : Measure Ω} {O : ℕ → Ω → 𝒳 × Bool × ℝ}

/-- `E[IF(O_0)²]` is the integral of `IF²` under the law of a record. -/
theorem integral_sq_comp_eq [IsProbabilityMeasure P] (hO : IsIIDSample O P)
    {f : 𝒳 × Bool × ℝ → ℝ} (hf : Measurable f) :
    P[fun ω => f (O 0 ω) ^ 2] = ∫ z, f z ^ 2 ∂(P.map (O 0)) :=
  (integral_map (hO.aemeasurable 0) (hf.pow_const 2).aestronglyMeasurable).symm

/-- **Bootstrap coverage for the weighted arm mean.** Under the hypotheses of the asymptotic
normality theorem (an i.i.d. sample, a measurable feature with `‖φ(x) - t‖ ≤ B`, the margin
condition, `P(A = a) > 0` and `E Y² < ∞`) and `σ² = weightedArmVariance > 0`, the bootstrap
percentile and basic intervals cover the weighted
arm mean `m₀` under the population tilt with probability tending to `1 - α`. -/
theorem tendsto_bootstrapArmMean_coverage [IsProbabilityMeasure P]
    (hO : IsIIDSample O P) {φ : 𝒳 → Fin p → ℝ} (hφ : Measurable φ) {t : Fin p → ℝ} {B : ℝ}
    (hB : ∀ x, ‖φ x - t‖ ≤ B) {δ : ℝ} (hδ : 0 < δ) (hmargin : ∀ v : Fin p → ℝ, ‖v‖ = 1 →
      δ ≤ (P.map (O 0)).real {z | δ ≤ v ⬝ᵥ (φ z.1 - t)}) (a : Bool)
    (hq : 0 < (P.map (O 0)).real {z | z.2.1 = a})
    (hy : MemLp (fun z : 𝒳 × Bool × ℝ => z.2.2) 2 (P.map (O 0)))
    (hσ : 0 < weightedArmVariance (P.map (O 0)) φ t a) {α z : ℝ}
    (hα : α ∈ Ioo (0 : ℝ) 1) (hz : cdf (gaussianReal 0 1) z = 1 - α / 2) :
    Tendsto (fun n => P.real {ω | tiltArmMean (P.map (O 0)) φ t a
        (tiltMinimizer (P.map (O 0)) φ t) ∈
          percentileInterval (bootstrapLaw (bootstrapArmMean φ t a) O n ω) α}) atTop
        (𝓝 (1 - α)) ∧
      Tendsto (fun n => P.real {ω | tiltArmMean (P.map (O 0)) φ t a
        (tiltMinimizer (P.map (O 0)) φ t) ∈
          basicInterval (bootstrapLaw (bootstrapArmMean φ t a) O n ω)
            (sampleBalancedArmMean φ t O a n ω) α}) atTop (𝓝 (1 - α)) := by
  have hAL := sampleBalancedArmMean_isAsymptoticallyLinear hO hφ hB hδ hmargin a hq hy
  have hlin := isBootstrapLinear_bootstrapArmMean hO hφ hB hδ hmargin a hq hy
  refine hlin.tendsto_coverage hO (measurable_bootstrapArmMean hφ t a) hAL ?_ hα hz
  rwa [integral_sq_comp_eq hO hAL.measurable]

/-- **Bootstrap coverage for the anchored comparison on the identity scale.** Under the
hypotheses of the asymptotic normality theorem for both arms and a positive variance
`E[(IF_false - IF_true)²] > 0` of the index part, the
bootstrap percentile and basic intervals of `(m*_false - m*_true) - d` cover
`(m₀_false - m₀_true) - d` with probability tending to `1 - α`, for a reported aggregate
comparison `d` that is held fixed under resampling. -/
theorem tendsto_bootstrapIndexContrast_coverage [IsProbabilityMeasure P]
    (hO : IsIIDSample O P) {φ : 𝒳 → Fin p → ℝ} (hφ : Measurable φ) {t : Fin p → ℝ} {B : ℝ}
    (hB : ∀ x, ‖φ x - t‖ ≤ B) {δ : ℝ} (hδ : 0 < δ) (hmargin : ∀ v : Fin p → ℝ, ‖v‖ = 1 →
      δ ≤ (P.map (O 0)).real {z | δ ≤ v ⬝ᵥ (φ z.1 - t)})
    (hq : ∀ a, 0 < (P.map (O 0)).real {z | z.2.1 = a})
    (hy : MemLp (fun z : 𝒳 × Bool × ℝ => z.2.2) 2 (P.map (O 0)))
    (d : ℝ)
    (hσ : 0 < ∫ z, (weightedArmInfluence (P.map (O 0)) φ t false z -
      weightedArmInfluence (P.map (O 0)) φ t true z) ^ 2 ∂(P.map (O 0))) {α z : ℝ}
    (hα : α ∈ Ioo (0 : ℝ) 1) (hz : cdf (gaussianReal 0 1) z = 1 - α / 2) :
    Tendsto (fun n => P.real {ω |
        tiltArmMean (P.map (O 0)) φ t false (tiltMinimizer (P.map (O 0)) φ t) -
          tiltArmMean (P.map (O 0)) φ t true (tiltMinimizer (P.map (O 0)) φ t) - d ∈
        percentileInterval (bootstrapLaw (fun n y => bootstrapArmMean φ t false n y -
          bootstrapArmMean φ t true n y - d) O n ω) α}) atTop (𝓝 (1 - α)) ∧
      Tendsto (fun n => P.real {ω |
        tiltArmMean (P.map (O 0)) φ t false (tiltMinimizer (P.map (O 0)) φ t) -
          tiltArmMean (P.map (O 0)) φ t true (tiltMinimizer (P.map (O 0)) φ t) - d ∈
        basicInterval (bootstrapLaw (fun n y => bootstrapArmMean φ t false n y -
          bootstrapArmMean φ t true n y - d) O n ω)
          (sampleBalancedArmMean φ t O false n ω - sampleBalancedArmMean φ t O true n ω - d)
          α}) atTop (𝓝 (1 - α)) := by
  have hF := sampleBalancedArmMean_isAsymptoticallyLinear hO hφ hB hδ hmargin false (hq false) hy
  have hT := sampleBalancedArmMean_isAsymptoticallyLinear hO hφ hB hδ hmargin true (hq true) hy
  have hAL := (hF.sub hT).sub (IsAsymptoticallyLinear.const P O d)
  have hlin := fun a => isBootstrapLinear_bootstrapArmMean hO hφ hB hδ hmargin a (hq a) hy
  have hL := ((hlin false).sub (hlin true)).sub (IsBootstrapLinear.const P O d)
  have hm : Measurable fun z => weightedArmInfluence (P.map (O 0)) φ t false z -
      weightedArmInfluence (P.map (O 0)) φ t true z - 0 :=
    (hF.measurable.sub hT.measurable).sub measurable_const
  refine hL.tendsto_coverage hO (fun n => ((measurable_bootstrapArmMean hφ t false n).sub
    (measurable_bootstrapArmMean hφ t true n)).sub_const d) hAL ?_ hα hz
  rw [integral_sq_comp_eq hO hm]
  simpa only [sub_zero] using hσ

/-- **Bootstrap coverage for the unanchored comparison on the identity scale.** Under the
hypotheses of the asymptotic normality theorem for the arm `true` and `σ² > 0`, the bootstrap
percentile and basic intervals of `c - m*_true`
cover `c - m₀_true` with probability tending to `1 - α`, for a reported aggregate mean `c` that
is held fixed under resampling. -/
theorem tendsto_bootstrapUnanchored_coverage [IsProbabilityMeasure P]
    (hO : IsIIDSample O P) {φ : 𝒳 → Fin p → ℝ} (hφ : Measurable φ) {t : Fin p → ℝ} {B : ℝ}
    (hB : ∀ x, ‖φ x - t‖ ≤ B) {δ : ℝ} (hδ : 0 < δ) (hmargin : ∀ v : Fin p → ℝ, ‖v‖ = 1 →
      δ ≤ (P.map (O 0)).real {z | δ ≤ v ⬝ᵥ (φ z.1 - t)})
    (hq : 0 < (P.map (O 0)).real {z | z.2.1 = true})
    (hy : MemLp (fun z : 𝒳 × Bool × ℝ => z.2.2) 2 (P.map (O 0)))
    (c : ℝ)
    (hσ : 0 < weightedArmVariance (P.map (O 0)) φ t true) {α z : ℝ}
    (hα : α ∈ Ioo (0 : ℝ) 1) (hz : cdf (gaussianReal 0 1) z = 1 - α / 2) :
    Tendsto (fun n => P.real {ω |
        c - tiltArmMean (P.map (O 0)) φ t true (tiltMinimizer (P.map (O 0)) φ t) ∈
        percentileInterval (bootstrapLaw (fun n y => c - bootstrapArmMean φ t true n y) O n ω)
          α}) atTop (𝓝 (1 - α)) ∧
      Tendsto (fun n => P.real {ω |
        c - tiltArmMean (P.map (O 0)) φ t true (tiltMinimizer (P.map (O 0)) φ t) ∈
        basicInterval (bootstrapLaw (fun n y => c - bootstrapArmMean φ t true n y) O n ω)
          (c - sampleBalancedArmMean φ t O true n ω) α}) atTop (𝓝 (1 - α)) := by
  have hT := sampleBalancedArmMean_isAsymptoticallyLinear hO hφ hB hδ hmargin true hq hy
  have hAL := (IsAsymptoticallyLinear.const P O c).sub hT
  have hL := (IsBootstrapLinear.const P O c).sub
    (isBootstrapLinear_bootstrapArmMean hO hφ hB hδ hmargin true hq hy)
  have hm : Measurable fun z => 0 - weightedArmInfluence (P.map (O 0)) φ t true z :=
    measurable_const.sub hT.measurable
  refine hL.tendsto_coverage hO (fun n => (measurable_bootstrapArmMean hφ t true n).const_sub c)
    hAL ?_ hα hz
  rw [integral_sq_comp_eq hO hm]
  simpa only [zero_sub, neg_sq, weightedArmVariance] using hσ

omit [MeasurableSpace 𝒳] in
/-- **The weighted arm mean of a balanced sample under an affine outcome.** If the sample `y`
admits positive balancing weights, has a record in arm `a`, and
`1{aᵢ = a} (yᵢ - m) = γᵀ (φ(xᵢ) - t)` for every record, then its weighted arm mean is `m`
exactly: the weighted residual `∑ᵢ wᵢ 1{aᵢ = a} (yᵢ - m) = γᵀ ∑ᵢ wᵢ (φ(xᵢ) - t)` vanishes by
balance. -/
theorem bootstrapArmMean_eq_of_affine {φ : 𝒳 → Fin p → ℝ} {t : Fin p → ℝ} {a : Bool} {n : ℕ}
    {y : Fin n → 𝒳 × Bool × ℝ} {m : ℝ} {γ : Fin p → ℝ}
    (hfeas : ∃ q ∈ balancingSet (fun i : Fin n => φ (y i).1 - t), ∀ i, 0 < q i)
    (harm : ∃ i, (y i).2.1 = a)
    (haff : ∀ i, armIndObs a (y i) * ((y i).2.2 - m) = γ ⬝ᵥ (φ (y i).1 - t)) :
    bootstrapArmMean φ t a n y = m := by
  rw [bootstrapArmMean_eq_div]
  set β := bootstrapTilt φ t n y with hβ
  have hbal := momentBalanced_dualMinimizer hfeas
  have hw : ∀ i, tiltWeight φ t 0 β (y i).1 = Real.exp (β ⬝ᵥ (φ (y i).1 - t)) := fun i => by
    simp [tiltWeight]
  have hj : ∀ j, ∑ i, Real.exp (β ⬝ᵥ (φ (y i).1 - t)) * (φ (y i).1 - t) j = 0 := by
    intro j
    have := congrFun hbal j
    simpa [MomentBalanced, Finset.sum_apply, sub_zero, smul_eq_mul, hβ, bootstrapTilt]
      using this
  have hterm : ∀ i, armIndObs a (y i) * tiltWeight φ t 0 β (y i).1 * (y i).2.2 -
      m * (armIndObs a (y i) * tiltWeight φ t 0 β (y i).1) =
        ∑ j, γ j * (Real.exp (β ⬝ᵥ (φ (y i).1 - t)) * (φ (y i).1 - t) j) := by
    intro i
    rw [hw]
    calc _ = Real.exp (β ⬝ᵥ (φ (y i).1 - t)) * (armIndObs a (y i) * ((y i).2.2 - m)) := by
          ring
      _ = Real.exp (β ⬝ᵥ (φ (y i).1 - t)) * (γ ⬝ᵥ (φ (y i).1 - t)) := by rw [haff i]
      _ = _ := by
          simp only [dotProduct, Finset.mul_sum]
          exact Finset.sum_congr rfl fun j _ => by ring
  have hnum : ∑ i, armIndObs a (y i) * tiltWeight φ t 0 β (y i).1 * (y i).2.2 =
      m * ∑ i, armIndObs a (y i) * tiltWeight φ t 0 β (y i).1 := by
    rw [← sub_eq_zero, Finset.mul_sum, ← Finset.sum_sub_distrib,
      Finset.sum_congr rfl fun i _ => hterm i, Finset.sum_comm]
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [← Finset.mul_sum, hj j, mul_zero]
  obtain ⟨i₀, hi₀⟩ := harm
  have hden : 0 < ∑ i, armIndObs a (y i) * tiltWeight φ t 0 β (y i).1 := by
    refine lt_of_lt_of_le ?_ (Finset.single_le_sum (fun i _ => ?_) (Finset.mem_univ i₀))
    · simp [armIndObs, hi₀, tiltWeight, Real.exp_pos]
    · exact mul_nonneg (by unfold armIndObs; split_ifs <;> norm_num) (Real.exp_pos _).le
  have hn : (n : ℝ) ≠ 0 := by have := i₀.pos; positivity
  simp only [resampleMean]
  rw [hnum]
  field_simp

end PopulationAdjustment

end CausalInference
