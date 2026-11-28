/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.PopulationAdjustment.WeightedNormalityVarianceMeasurable
public import CausalInference.PopulationAdjustment.WeightedNormalityContrast
public import CausalInference.Estimation.ConfidenceInterval

/-!
# Wald intervals for the weighted arm mean and the unanchored comparison

The sandwich variance estimate `σ̂ₙ²` of the weighted (matching adjusted) arm mean is consistent
(`sandwichMatrixHat_weighted_tendstoInMeasure`) and a measurable function of the sample
(`isSampleMeasurable_weightedInfluenceCovHat`), so the Wald interval
`m̂ₙ ± z σ̂ₙ / √n` built from the asymptotic normality of the weighted arm mean has asymptotic
coverage `1 - α` (`tendsto_waldInterval_coverage`), provided the limiting variance is positive.
The same holds for the unanchored comparison `g(m̂_B) - g(m̂ₙ)` on a link scale `g`, with the
delta method variance estimate `g'(m̂ₙ)² σ̂ₙ² + ŵₙ`, where `ŵₙ` is a consistent estimate of the
asymptotic variance of the aggregate part.

Under the consistency and identification conditions of
`sampleBalancedArmMean_isConsistent_armMean` (randomization, an arm regression affine in the
features, and target moments `t` equal to the feature means of the target population) the
covered limit is the marginal mean `Q.armMean ta` of the target population.

## Main definitions

* `weightedArmSdHat`: `σ̂ₙ`, the square root of the sandwich variance estimate.
* `unanchoredSdHat`: the square root of `g'(m̂ₙ)² σ̂ₙ² + ŵₙ`.

## Main results

* `weightedArmSdHat_isConsistent`, `isSampleMeasurable_weightedArmSdHat`.
* `tendsto_weightedArm_waldInterval_coverage`: coverage of the tilted arm mean.
* `tendsto_weightedArm_waldInterval_coverage_armMean`: coverage of the marginal mean of the
  target population.
* `tendsto_unanchored_waldInterval_coverage` and
  `tendsto_unanchored_waldInterval_coverage_armMean`: the same for the unanchored comparison.

## References

* Signorovitch, Wu, Yu, Gerrits, Kantor, Cai, Gupta, Mulani, *Comparative effectiveness without
  head-to-head trials* (2010).
* Stefanski, Boos, *The calculus of M-estimation* (2002).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Finset Matrix
open scoped Topology ENNReal NNReal

namespace CausalInference

namespace PopulationAdjustment

open PointTreatment IndirectComparison

variable {𝒳 : Type*} {p : ℕ} [MeasurableSpace 𝒳] {Ω : Type*} [MeasurableSpace Ω]
  {P : Measure Ω} {O : ℕ → Ω → 𝒳 × Bool × ℝ}

/-- The **sandwich standard error** `σ̂ₙ` of the weighted arm mean of arm `a`: the square root of
the sandwich variance estimate `(n Σ̂ₙ)_{m m} = n⁻¹ ∑ᵢ ÎF(Zᵢ)²`. -/
noncomputable def weightedArmSdHat (φ : 𝒳 → Fin p → ℝ) (t : Fin p → ℝ)
    (O : ℕ → Ω → 𝒳 × Bool × ℝ) (a : Bool) (n : ℕ) (ω : Ω) : ℝ :=
  √(weightedInfluenceCovHat φ t O a a n ω)

/-- The diagonal cross covariance estimate is consistent for the limiting variance. -/
theorem weightedInfluenceCovHat_self_tendstoInMeasure [IsProbabilityMeasure P]
    (hO : IsIIDSample O P) {φ : 𝒳 → Fin p → ℝ} (hφ : Measurable φ) {t : Fin p → ℝ} {B : ℝ}
    (hB : ∀ x, ‖φ x - t‖ ≤ B) {δ : ℝ} (hδ : 0 < δ) (hmargin : ∀ v : Fin p → ℝ, ‖v‖ = 1 →
      δ ≤ (P.map (O 0)).real {z | δ ≤ v ⬝ᵥ (φ z.1 - t)}) (a : Bool)
    (hq : 0 < (P.map (O 0)).real {z | z.2.1 = a})
    (hy : MemLp (fun z : 𝒳 × Bool × ℝ => z.2.2) 2 (P.map (O 0))) :
    TendstoInMeasure P (weightedInfluenceCovHat φ t O a a) atTop
      (fun _ => weightedArmVariance (P.map (O 0)) φ t a) := by
  have he : weightedInfluenceCovHat φ t O a a = fun (n : ℕ) ω =>
      ((n : ℝ) • sandwichMatrixHat O (weightedEstFun φ t a) (weightedEstJac φ t a)
        (weightedStackedEstimate φ t O a) n ω) (Sum.inr ()) (Sum.inr ()) :=
    funext fun n => funext fun ω => weightedInfluenceCovHat_self φ t O a n ω
  rw [he]
  exact sandwichMatrixHat_weighted_tendstoInMeasure hO hφ hB hδ hmargin a hq hy

/-- **Consistency of the sandwich standard error**: `σ̂ₙ → √σ²` in probability. -/
theorem weightedArmSdHat_isConsistent [IsProbabilityMeasure P]
    (hO : IsIIDSample O P) {φ : 𝒳 → Fin p → ℝ} (hφ : Measurable φ) {t : Fin p → ℝ} {B : ℝ}
    (hB : ∀ x, ‖φ x - t‖ ≤ B) {δ : ℝ} (hδ : 0 < δ) (hmargin : ∀ v : Fin p → ℝ, ‖v‖ = 1 →
      δ ≤ (P.map (O 0)).real {z | δ ≤ v ⬝ᵥ (φ z.1 - t)}) (a : Bool)
    (hq : 0 < (P.map (O 0)).real {z | z.2.1 = a})
    (hy : MemLp (fun z : 𝒳 × Bool × ℝ => z.2.2) 2 (P.map (O 0))) :
    IsConsistent (weightedArmSdHat φ t O a) (√(weightedArmVariance (P.map (O 0)) φ t a)) P :=
  (weightedInfluenceCovHat_self_tendstoInMeasure hO hφ hB hδ hmargin a hq hy).comp_continuousAt
    Real.continuous_sqrt.continuousAt

omit [MeasurableSpace Ω] in
/-- **The sandwich standard error is a measurable function of the sample.** -/
theorem isSampleMeasurable_weightedArmSdHat {φ : 𝒳 → Fin p → ℝ} (hφ : Measurable φ)
    (t : Fin p → ℝ) (O : ℕ → Ω → 𝒳 × Bool × ℝ) (a : Bool) :
    IsSampleMeasurable (weightedArmSdHat φ t O a) O := fun n => by
  obtain ⟨g, hg, e⟩ := isSampleMeasurable_weightedInfluenceCovHat hφ t O a a n
  exact ⟨fun x => √(g x), hg.sqrt, by
    funext ω
    simp only [weightedArmSdHat, e]⟩

/-- **Asymptotic coverage of the Wald interval for the weighted arm mean.** Under the hypotheses
of the normal limit (`sampleBalancedArmMean_tendstoInDistribution`), and when the limiting
variance `σ² = weightedArmVariance` is positive, the interval `m̂ₙ ± z σ̂ₙ / √n` with the sandwich
standard error covers the tilted arm mean with probability tending to `1 - α`, where
`Φ(z) = 1 - α / 2`. -/
theorem tendsto_weightedArm_waldInterval_coverage [IsProbabilityMeasure P]
    (hO : IsIIDSample O P) {φ : 𝒳 → Fin p → ℝ} (hφ : Measurable φ) {t : Fin p → ℝ} {B : ℝ}
    (hB : ∀ x, ‖φ x - t‖ ≤ B) {δ : ℝ} (hδ : 0 < δ) (hmargin : ∀ v : Fin p → ℝ, ‖v‖ = 1 →
      δ ≤ (P.map (O 0)).real {z | δ ≤ v ⬝ᵥ (φ z.1 - t)}) (a : Bool)
    (hq : 0 < (P.map (O 0)).real {z | z.2.1 = a})
    (hy : MemLp (fun z : 𝒳 × Bool × ℝ => z.2.2) 2 (P.map (O 0)))
    (hV : 0 < weightedArmVariance (P.map (O 0)) φ t a) {z α : ℝ} (hz : 0 ≤ z)
    (hzα : cdf (gaussianReal 0 1) z = 1 - α / 2) :
    Tendsto (fun n => P.real {ω | tiltArmMean (P.map (O 0)) φ t a
      (tiltMinimizer (P.map (O 0)) φ t) ∈ waldInterval (sampleBalancedArmMean φ t O a n ω)
        (weightedArmSdHat φ t O a n ω) z n}) atTop (𝓝 (1 - α)) := by
  set V := weightedArmVariance (P.map (O 0)) φ t a
  have hAN := sampleBalancedArmMean_tendstoInDistribution hO hφ hB hδ hmargin a hq hy
    (HasLaw.id (μ := gaussianReal 0 V.toNNReal))
  have hY : HasLaw id (gaussianReal 0 ((√V) ^ 2).toNNReal) (gaussianReal 0 V.toNNReal) := by
    rw [Real.sq_sqrt hV.le]
    exact HasLaw.id
  exact tendsto_waldInterval_coverage (Real.sqrt_pos.2 hV) hz hzα hY hAN
    (weightedArmSdHat_isConsistent hO hφ hB hδ hmargin a hq hy)
    ((isSampleMeasurable_weightedArmSdHat hφ t O a).aemeasurable hO)

/-- **Coverage of any consistency limit.** If the weighted arm mean is consistent for `L`, the
Wald interval covers `L` with probability tending to `1 - α`: the tilted arm mean equals `L`
(`tiltArmMean_eq_of_isConsistent`). -/
theorem tendsto_weightedArm_waldInterval_coverage_of_isConsistent [IsProbabilityMeasure P]
    (hO : IsIIDSample O P) {φ : 𝒳 → Fin p → ℝ} (hφ : Measurable φ) {t : Fin p → ℝ} {B : ℝ}
    (hB : ∀ x, ‖φ x - t‖ ≤ B) {δ : ℝ} (hδ : 0 < δ) (hmargin : ∀ v : Fin p → ℝ, ‖v‖ = 1 →
      δ ≤ (P.map (O 0)).real {z | δ ≤ v ⬝ᵥ (φ z.1 - t)}) (a : Bool)
    (hq : 0 < (P.map (O 0)).real {z | z.2.1 = a})
    (hy : MemLp (fun z : 𝒳 × Bool × ℝ => z.2.2) 2 (P.map (O 0)))
    (hV : 0 < weightedArmVariance (P.map (O 0)) φ t a) {z α : ℝ} (hz : 0 ≤ z)
    (hzα : cdf (gaussianReal 0 1) z = 1 - α / 2) {L : ℝ}
    (hL : IsConsistent (sampleBalancedArmMean φ t O a) L P) :
    Tendsto (fun n => P.real {ω | L ∈ waldInterval (sampleBalancedArmMean φ t O a n ω)
        (weightedArmSdHat φ t O a n ω) z n}) atTop (𝓝 (1 - α)) := by
  rw [← tiltArmMean_eq_of_isConsistent hO hφ hB hδ hmargin a hq (hy.integrable one_le_two) hL]
  exact tendsto_weightedArm_waldInterval_coverage hO hφ hB hδ hmargin a hq hy hV hz hzα

/-- **A square integrable outcome has a square integrable regression residual**: the
regression surface is almost everywhere a conditional expectation of the outcome, which is square
integrable, so `Y - μ_A(X)` is square integrable. -/
theorem integrable_residual_sq_of_memLp {ν : Measure (𝒳 × Bool × ℝ)} [IsFiniteMeasure ν]
    {mu : Bool → 𝒳 → ℝ} (hy : MemLp (fun z : 𝒳 × Bool × ℝ => z.2.2) 2 ν)
    (hreg : ν[fun z => z.2.2 | MeasurableSpace.comap
      (fun z : 𝒳 × Bool × ℝ => (z.1, z.2.1)) inferInstance] =ᵐ[ν] fun z => mu z.2.1 z.1) :
    Integrable (fun z : 𝒳 × Bool × ℝ => (z.2.2 - mu z.2.1 z.1) ^ 2) ν := by
  have h1 := hy.condExp (m := MeasurableSpace.comap (fun z : 𝒳 × Bool × ℝ => (z.1, z.2.1))
    inferInstance) one_le_two
  have h2 : MemLp (fun z : 𝒳 × Bool × ℝ => mu z.2.1 z.1) 2 ν := h1.ae_eq hreg
  exact (hy.sub h2).integrable_sq

/-- **Coverage of the marginal mean of the target population.** Under randomization of the
index trial, an arm regression `mu a` affine in the features, square integrable outcomes, target
moments `t` equal to the feature means of the target population `Q`, and the conditional mean of
the potential outcome `Q.Y ta` given the features equal to `mu a`, the Wald interval with the
sandwich standard error covers `Q.armMean ta` with probability tending to `1 - α`. The residual
is square integrable because the outcome is (`integrable_residual_sq_of_memLp`). -/
theorem tendsto_weightedArm_waldInterval_coverage_armMean [IsProbabilityMeasure P]
    {Ω' ι : Type*} [MeasurableSpace Ω'] (hO : IsIIDSample O P) (hOm : ∀ i, Measurable (O i))
    {φ : 𝒳 → Fin p → ℝ} (hφ : Measurable φ) {t : Fin p → ℝ} {B : ℝ} (hB : ∀ x, ‖φ x - t‖ ≤ B)
    {δ : ℝ} (hδ : 0 < δ) (hmargin : ∀ v : Fin p → ℝ, ‖v‖ = 1 →
      δ ≤ (P.map (O 0)).real {z | δ ≤ v ⬝ᵥ (φ z.1 - t)})
    (hind : IndepFun (fun z : 𝒳 × Bool × ℝ => z.1) (fun z => z.2.1) (P.map (O 0))) (a : Bool)
    (hq : 0 < (P.map (O 0)).real {z | z.2.1 = a})
    (hy : MemLp (fun z : 𝒳 × Bool × ℝ => z.2.2) 2 (P.map (O 0)))
    {mu : Bool → 𝒳 → ℝ} (hmu : ∀ s, Measurable (mu s))
    (hreg : (P.map (O 0))[fun z => z.2.2 | MeasurableSpace.comap
      (fun z : 𝒳 × Bool × ℝ => (z.1, z.2.1)) inferInstance] =ᵐ[P.map (O 0)]
        fun z => mu z.2.1 z.1) {σ2 : ℝ}
    (hvar : (P.map (O 0))[fun z => (z.2.2 - mu z.2.1 z.1) ^ 2 |
      MeasurableSpace.comap (fun z : 𝒳 × Bool × ℝ => (z.1, z.2.1)) inferInstance]
        ≤ᵐ[P.map (O 0)] fun _ => σ2)
    {a0 : ℝ} {b : Fin p → ℝ} (haff : ∀ x, mu a x = a0 + b ⬝ᵥ φ x)
    {Q : Population Ω' 𝒳 ι} [IsProbabilityMeasure Q.μ] (hQX : Measurable Q.X)
    (ht : ∀ k, ∫ x, φ x k ∂Q.covLaw = t k) {ta : ι} (hQY : Integrable (Q.Y ta) Q.μ)
    (hQm : Q.IsCondMean ta (mu a))
    (hV : 0 < weightedArmVariance (P.map (O 0)) φ t a) {z α : ℝ} (hz : 0 ≤ z)
    (hzα : cdf (gaussianReal 0 1) z = 1 - α / 2) :
    Tendsto (fun n => P.real {ω | Q.armMean ta ∈ waldInterval (sampleBalancedArmMean φ t O a n ω)
        (weightedArmSdHat φ t O a n ω) z n}) atTop (𝓝 (1 - α)) := by
  have : IsProbabilityMeasure (P.map (O 0)) :=
    (Measure.isProbabilityMeasure_map_iff (hO.aemeasurable 0)).2 inferInstance
  exact tendsto_weightedArm_waldInterval_coverage_of_isConsistent hO hφ hB hδ hmargin a hq hy hV
    hz hzα (sampleBalancedArmMean_isConsistent_armMean hO hOm hφ hB hδ hmargin hind a hq hmu
      (integrable_residual_sq_of_memLp hy hreg) hreg hvar haff hQX ht hQY hQm)

/-! ### The unanchored comparison -/

/-- The **delta method standard error of the unanchored comparison**
`√(g'(m̂ₙ)² σ̂ₙ² + ŵₙ)`, with the derivative `dg` of the link, the sandwich variance estimate of
the index arm and an estimate `ŵₙ` of the asymptotic variance of the aggregate part. -/
noncomputable def unanchoredSdHat (dg : ℝ → ℝ) (φ : 𝒳 → Fin p → ℝ) (t : Fin p → ℝ)
    (O : ℕ → Ω → 𝒳 × Bool × ℝ) (wHat : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  √(dg (sampleBalancedArmMean φ t O true n ω) ^ 2 * weightedInfluenceCovHat φ t O true true n ω +
    wHat n ω)

/-- The law `N(0, (√(s + w))²)` is the law `N(0, s⁺ + w)` of the comparison limit. -/
theorem gaussianReal_sq_sqrt_add {s : ℝ} (hs : 0 ≤ s) (w : ℝ≥0) :
    gaussianReal 0 ((√(s + w)) ^ 2).toNNReal = gaussianReal 0 (s.toNNReal + w) := by
  rw [Real.sq_sqrt (add_nonneg hs w.coe_nonneg), Real.toNNReal_add hs w.coe_nonneg,
    Real.toNNReal_coe]

/-- **Asymptotic coverage of the Wald interval for the unanchored comparison.** Under the
hypotheses of `unanchoredBalancedEstimate_tendstoInDistribution` with the derivative
`g'(m_T) = dg m_T` of the link, a measurable `dg` continuous at `m_T`, an estimate `ŵₙ` of the
aggregate variance `w` that is consistent and almost everywhere measurable, and a positive total
variance `g'(m_T)² σ_T² + w`, the interval `(g(m̂_B) - g(m̂ₙ)) ± z ŝₙ / √n` with
`ŝₙ = unanchoredSdHat` covers `g(m_B) - g(m_T)` with probability tending to `1 - α`. -/
theorem tendsto_unanchored_waldInterval_coverage [IsProbabilityMeasure P]
    (hO : IsIIDSample O P) {φ : 𝒳 → Fin p → ℝ} (hφ : Measurable φ) {t : Fin p → ℝ} {B : ℝ}
    (hB : ∀ x, ‖φ x - t‖ ≤ B) {δ : ℝ} (hδ : 0 < δ) (hmargin : ∀ v : Fin p → ℝ, ‖v‖ = 1 →
      δ ≤ (P.map (O 0)).real {z | δ ≤ v ⬝ᵥ (φ z.1 - t)})
    (hq : 0 < (P.map (O 0)).real {z | z.2.1 = true})
    (hy : MemLp (fun z : 𝒳 × Bool × ℝ => z.2.2) 2 (P.map (O 0))) {g dg : ℝ → ℝ}
    (hg : Measurable g) (hdg : Measurable dg)
    (hgt : HasDerivAt g (dg (tiltArmMean (P.map (O 0)) φ t true (tiltMinimizer (P.map (O 0)) φ t)))
      (tiltArmMean (P.map (O 0)) φ t true (tiltMinimizer (P.map (O 0)) φ t)))
    (hdgc : ContinuousAt dg
      (tiltArmMean (P.map (O 0)) φ t true (tiltMinimizer (P.map (O 0)) φ t)))
    {mB : ℕ → Ω → ℝ} {mB₀ : ℝ}
    (hindep : ∀ n, IndepFun (fun ω (i : Fin n) => O i ω) (mB n) P)
    {Ω₂ : Type*} [MeasurableSpace Ω₂] {P₂ : Measure Ω₂} [IsProbabilityMeasure P₂] {Y₂ : Ω₂ → ℝ}
    {w : ℝ≥0}
    (hagg : TendstoInDistribution (fun (n : ℕ) ω => √n * (g (mB n ω) - g mB₀)) atTop Y₂
      (fun _ => P) P₂) (hY₂ : HasLaw Y₂ (gaussianReal 0 w) P₂)
    {wHat : ℕ → Ω → ℝ} (hwHat : IsConsistent wHat w P) (hwm : ∀ n, AEMeasurable (wHat n) P)
    (hσ : 0 < dg (tiltArmMean (P.map (O 0)) φ t true (tiltMinimizer (P.map (O 0)) φ t)) ^ 2 *
      weightedArmVariance (P.map (O 0)) φ t true + w) {z α : ℝ} (hz : 0 ≤ z)
    (hzα : cdf (gaussianReal 0 1) z = 1 - α / 2) :
    Tendsto (fun n => P.real {ω | g mB₀ - g (tiltArmMean (P.map (O 0)) φ t true
      (tiltMinimizer (P.map (O 0)) φ t)) ∈ waldInterval (unanchoredBalancedEstimate g φ t O mB n ω)
        (unanchoredSdHat dg φ t O wHat n ω) z n}) atTop (𝓝 (1 - α)) := by
  set mT := tiltArmMean (P.map (O 0)) φ t true (tiltMinimizer (P.map (O 0)) φ t)
  set V := weightedArmVariance (P.map (O 0)) φ t true
  have hs : 0 ≤ dg mT ^ 2 * V := mul_nonneg (sq_nonneg _) (weightedArmVariance_nonneg _ _ _ _)
  have hAN := unanchoredBalancedEstimate_tendstoInDistribution hO hφ hB hδ hmargin hq hy hg hgt
    hindep (HasLaw.id (μ := gaussianReal 0 (dg mT ^ 2 * V).toNNReal)) hagg hY₂
    (HasLaw.id (μ := gaussianReal 0 ((dg mT ^ 2 * V).toNNReal + w)))
  have hY : HasLaw id (gaussianReal 0 ((√(dg mT ^ 2 * V + w)) ^ 2).toNNReal)
      (gaussianReal 0 ((dg mT ^ 2 * V).toNNReal + w)) := by
    rw [gaussianReal_sq_sqrt_add hs]
    exact HasLaw.id
  have hm := sampleBalancedArmMean_tendstoInMeasure hO hφ hB hδ hmargin true hq
    (hy.integrable one_le_two)
  have hC := weightedInfluenceCovHat_self_tendstoInMeasure hO hφ hB hδ hmargin true hq hy
  have hcons : IsConsistent (unanchoredSdHat dg φ t O wHat) (√(dg mT ^ 2 * V + w)) P := by
    have h3 := ((hm.comp_continuousAt hdgc).prodMk hC).prodMk hwHat
    have hc : ContinuousAt (fun r : (ℝ × ℝ) × ℝ => √(r.1.1 ^ 2 * r.1.2 + r.2))
        ((dg mT, V), (w : ℝ)) := by fun_prop
    exact h3.comp_continuousAt hc
  have hSM : IsSampleMeasurable (fun n ω => dg (sampleBalancedArmMean φ t O true n ω) ^ 2 *
      weightedInfluenceCovHat φ t O true true n ω) O :=
    isSampleMeasurable_comp₂ (isSampleMeasurable_sampleBalancedArmMean hφ t O true)
      (isSampleMeasurable_weightedInfluenceCovHat hφ t O true true)
      (f := fun x c => dg x ^ 2 * c)
      (((hdg.comp measurable_fst).pow_const 2).mul measurable_snd)
  have hmeas : ∀ n, AEMeasurable (unanchoredSdHat dg φ t O wHat n) P := fun n =>
    ((hSM.aemeasurable hO n).add (hwm n)).sqrt
  exact tendsto_waldInterval_coverage (Real.sqrt_pos.2 hσ) hz hzα hY hAN hcons hmeas

/-- **Coverage of the unanchored comparison in the target population.** Under the conditions of
`tendsto_weightedArm_waldInterval_coverage_armMean` for the index arm `true` (randomization, an
affine regression of the index arm, target moments `t` equal to the feature means of `Q`, and
the conditional mean of `Q.Y ta` equal to that regression), the interval covers
`g(m_B) - g(Q.armMean ta)` with probability tending to `1 - α`. -/
theorem tendsto_unanchored_waldInterval_coverage_armMean [IsProbabilityMeasure P]
    {Ω' ι : Type*} [MeasurableSpace Ω'] (hO : IsIIDSample O P) (hOm : ∀ i, Measurable (O i))
    {φ : 𝒳 → Fin p → ℝ} (hφ : Measurable φ) {t : Fin p → ℝ} {B : ℝ} (hB : ∀ x, ‖φ x - t‖ ≤ B)
    {δ : ℝ} (hδ : 0 < δ) (hmargin : ∀ v : Fin p → ℝ, ‖v‖ = 1 →
      δ ≤ (P.map (O 0)).real {z | δ ≤ v ⬝ᵥ (φ z.1 - t)})
    (hind : IndepFun (fun z : 𝒳 × Bool × ℝ => z.1) (fun z => z.2.1) (P.map (O 0)))
    (hq : 0 < (P.map (O 0)).real {z | z.2.1 = true})
    (hy : MemLp (fun z : 𝒳 × Bool × ℝ => z.2.2) 2 (P.map (O 0)))
    {mu : Bool → 𝒳 → ℝ} (hmu : ∀ s, Measurable (mu s))
    (hreg : (P.map (O 0))[fun z => z.2.2 | MeasurableSpace.comap
      (fun z : 𝒳 × Bool × ℝ => (z.1, z.2.1)) inferInstance] =ᵐ[P.map (O 0)]
        fun z => mu z.2.1 z.1) {σ2 : ℝ}
    (hvar : (P.map (O 0))[fun z => (z.2.2 - mu z.2.1 z.1) ^ 2 |
      MeasurableSpace.comap (fun z : 𝒳 × Bool × ℝ => (z.1, z.2.1)) inferInstance]
        ≤ᵐ[P.map (O 0)] fun _ => σ2)
    {a0 : ℝ} {b : Fin p → ℝ} (haff : ∀ x, mu true x = a0 + b ⬝ᵥ φ x)
    {Q : Population Ω' 𝒳 ι} [IsProbabilityMeasure Q.μ] (hQX : Measurable Q.X)
    (ht : ∀ k, ∫ x, φ x k ∂Q.covLaw = t k) {ta : ι} (hQY : Integrable (Q.Y ta) Q.μ)
    (hQm : Q.IsCondMean ta (mu true)) {g dg : ℝ → ℝ}
    (hg : Measurable g) (hdg : Measurable dg)
    (hgt : HasDerivAt g (dg (Q.armMean ta)) (Q.armMean ta)) (hdgc : ContinuousAt dg (Q.armMean ta))
    {mB : ℕ → Ω → ℝ} {mB₀ : ℝ}
    (hindep : ∀ n, IndepFun (fun ω (i : Fin n) => O i ω) (mB n) P)
    {Ω₂ : Type*} [MeasurableSpace Ω₂] {P₂ : Measure Ω₂} [IsProbabilityMeasure P₂] {Y₂ : Ω₂ → ℝ}
    {w : ℝ≥0}
    (hagg : TendstoInDistribution (fun (n : ℕ) ω => √n * (g (mB n ω) - g mB₀)) atTop Y₂
      (fun _ => P) P₂) (hY₂ : HasLaw Y₂ (gaussianReal 0 w) P₂)
    {wHat : ℕ → Ω → ℝ} (hwHat : IsConsistent wHat w P) (hwm : ∀ n, AEMeasurable (wHat n) P)
    (hσ : 0 < dg (Q.armMean ta) ^ 2 * weightedArmVariance (P.map (O 0)) φ t true + w)
    {z α : ℝ} (hz : 0 ≤ z) (hzα : cdf (gaussianReal 0 1) z = 1 - α / 2) :
    Tendsto (fun n => P.real {ω | g mB₀ - g (Q.armMean ta) ∈
      waldInterval (unanchoredBalancedEstimate g φ t O mB n ω)
        (unanchoredSdHat dg φ t O wHat n ω) z n}) atTop (𝓝 (1 - α)) := by
  have : IsProbabilityMeasure (P.map (O 0)) :=
    (Measure.isProbabilityMeasure_map_iff (hO.aemeasurable 0)).2 inferInstance
  have hL := tiltArmMean_eq_of_isConsistent hO hφ hB hδ hmargin true hq (hy.integrable one_le_two)
    (sampleBalancedArmMean_isConsistent_armMean hO hOm hφ hB hδ hmargin hind true hq hmu
      (integrable_residual_sq_of_memLp hy hreg) hreg hvar haff hQX ht hQY hQm)
  rw [← hL] at hgt hdgc hσ ⊢
  exact tendsto_unanchored_waldInterval_coverage hO hφ hB hδ hmargin hq hy hg hdg hgt hdgc hindep
    hagg hY₂ hwHat hwm hσ hz hzα

end PopulationAdjustment

end CausalInference
