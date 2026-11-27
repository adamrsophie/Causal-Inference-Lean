/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.Estimation.Consistency
public import CausalInference.InstrumentalVariables.LinearIV

/-!
# Consistency of instrumental variable estimators

Probability setting: a general probability space `(Ω, μ)` carrying an i.i.d. sample
`O : ℕ → Ω → 𝒪` (`CausalInference.IsIIDSample`) on a measurable observation space `𝒪`. The
instrument, treatment and outcome are measurable real functions `z d y : 𝒪 → ℝ` of an
observation; for the Wald ratio the instrument is a measurable binary `zb : 𝒪 → Bool`. The
population quantities are those of the first observation `O 0`. Consistency is convergence in
probability (`CausalInference.IsConsistent`).

## Main definitions

* `CausalInference.sampleCov`: the plug-in sample covariance `P_n(fg) - P_n f · P_n g`.
* `CausalInference.sampleCovRatio`: the sample IV (covariance ratio) estimator
  `Ĉov(Z, Y) / Ĉov(Z, D)`.
* `CausalInference.sampleCondMean`: the sample mean of `x` among the observations with
  instrument value `b`.
* `CausalInference.sampleWald`: the sample Wald ratio, the difference in sample outcome means
  between the two instrument groups divided by the difference in sample treatment means.

## Main results

* `CausalInference.IsConsistent.div`: a ratio of consistent estimators is consistent for the
  ratio of the limits when the limit of the denominator is nonzero.
* `CausalInference.sampleCov_isConsistent`: the sample covariance is consistent under finite
  second moments.
* `CausalInference.sampleCovRatio_isConsistent`: the sample covariance ratio is consistent for
  `Cov(Z, Y) / Cov(Z, D)` when the first stage `Cov(Z, D)` is nonzero.
* `CausalInference.sampleCovRatio_isConsistent_beta`: in the linear model `Y = α + β D + U` with
  an exogenous and relevant instrument, the sample covariance ratio is consistent for `β`.
* `CausalInference.sampleWald_isConsistent`: the sample Wald ratio is consistent for the
  population Wald ratio `(E[Y | Z = 1] - E[Y | Z = 0]) / (E[D | Z = 1] - E[D | Z = 0])` when
  both instrument groups have positive probability and the first stage is nonzero; only
  integrability of `Y` and `D` is needed. `CausalInference.sampleWald_isConsistent_covRatio`:
  by `LinearIV.covRatio_eq_waldRatio` the same limit is the covariance ratio of the `0`/`1`
  coded instrument.
* What fails at a zero first stage: `CausalInference.IsConsistent.not_div_of_tendsto_zero` and
  `CausalInference.sampleCovRatio_not_isConsistent`. If `Cov(Z, D) = 0` but `Cov(Z, Y) ≠ 0`,
  the sample covariance ratio is consistent for no constant at all (in particular not for the
  totalized value `Cov(Z, Y) / 0 = 0`) unless the sample first stage is exactly zero with
  probability tending to one, that is unless only the convention `x / 0 = 0` is at work.
  `CausalInference.not_div_of_tendsto_zero_hypotheses_satisfiable` shows that the hypotheses
  of the abstract statement can hold together.

The finite sample bias of the IV estimator, which the source also mentions, is not formalized:
the ratio need not even have a finite mean.

Source: NICE Decision Support Unit Technical Support Document 17 (Faria, Hernandez Alava, Manca
and Wailoo, 2015), Section 2.4.1 and Section 4.2.2, Question 16 ("IV methods are biased on finite
samples but they are consistent in large samples"); A. Wald (1940), *The fitting of straight
lines if both variables are subject to error*; A. W. van der Vaart (1998), *Asymptotic
Statistics*, chapter 2.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter
open scoped Topology ENNReal

namespace CausalInference

variable {Ω 𝒪 : Type*} {mΩ : MeasurableSpace Ω} [MeasurableSpace 𝒪]

/-- **Ratio rule for consistency.** If `a` is consistent for `α`, `b` is consistent for `β` and
`β ≠ 0`, then `a / b` is consistent for `α / β`. -/
theorem IsConsistent.div {μ : Measure Ω} {a b : ℕ → Ω → ℝ} {α β : ℝ}
    (ha : IsConsistent a α μ) (hb : IsConsistent b β μ) (hβ : β ≠ 0) :
    IsConsistent (fun n ω ↦ a n ω / b n ω) (α / β) μ :=
  IsConsistent.comp₂ (g := (· / ·))
    (continuous_fst.continuousAt.div continuous_snd.continuousAt hβ) ha hb

/-- The plug-in sample covariance `n⁻¹ ∑ f (O i) g (O i) - (n⁻¹ ∑ f (O i)) (n⁻¹ ∑ g (O i))` of
the transformed observations `f (O i)` and `g (O i)`, with divisor `n`. At `n = 0` it is `0`. -/
noncomputable def sampleCov (f g : 𝒪 → ℝ) (O : ℕ → Ω → 𝒪) (n : ℕ) (ω : Ω) : ℝ :=
  sampleMean (fun x ↦ f x * g x) O n ω - sampleMean f O n ω * sampleMean g O n ω

/-- **Consistency of the sample covariance.** If `O` is an i.i.d. sample under a probability
measure `μ` and `f`, `g` are measurable with `f (O 0)`, `g (O 0)` of finite second moment, then
the sample covariance is consistent for `Cov(f (O 0), g (O 0))`. -/
theorem sampleCov_isConsistent {μ : Measure Ω} [IsProbabilityMeasure μ] {O : ℕ → Ω → 𝒪}
    (hO : IsIIDSample O μ) {f g : 𝒪 → ℝ} (hf : Measurable f) (hg : Measurable g)
    (hf2 : MemLp (fun ω ↦ f (O 0 ω)) 2 μ) (hg2 : MemLp (fun ω ↦ g (O 0 ω)) 2 μ) :
    IsConsistent (sampleCov f g O) (cov[fun ω ↦ f (O 0 ω), fun ω ↦ g (O 0 ω); μ]) μ := by
  have hfg := sampleMean_isConsistent hO (hf.mul hg) (hf2.integrable_mul hg2)
  have hm := (sampleMean_isConsistent hO hf (hf2.integrable one_le_two)).mul
    (sampleMean_isConsistent hO hg (hg2.integrable one_le_two))
  rw [covariance_eq_sub hf2 hg2]
  exact hfg.sub hm

/-- The sample IV estimator: the ratio `Ĉov(Z, Y) / Ĉov(Z, D)` of sample covariances, for the
instrument `z`, outcome `y` and treatment `d`. It is `0` when the sample first stage
`Ĉov(Z, D)` vanishes. -/
noncomputable def sampleCovRatio (z y d : 𝒪 → ℝ) (O : ℕ → Ω → 𝒪) (n : ℕ) (ω : Ω) : ℝ :=
  sampleCov z y O n ω / sampleCov z d O n ω

/-- **Consistency of the sample IV estimator.** For an i.i.d. sample under a probability
measure, measurable `z`, `y`, `d` with finite second moments and a nonzero first stage
`Cov(Z, D) ≠ 0`, the ratio of sample covariances is consistent for `Cov(Z, Y) / Cov(Z, D)`. -/
theorem sampleCovRatio_isConsistent {μ : Measure Ω} [IsProbabilityMeasure μ] {O : ℕ → Ω → 𝒪}
    (hO : IsIIDSample O μ) {z y d : 𝒪 → ℝ} (hz : Measurable z) (hy : Measurable y)
    (hd : Measurable d) (hz2 : MemLp (fun ω ↦ z (O 0 ω)) 2 μ)
    (hy2 : MemLp (fun ω ↦ y (O 0 ω)) 2 μ) (hd2 : MemLp (fun ω ↦ d (O 0 ω)) 2 μ)
    (hR : cov[fun ω ↦ z (O 0 ω), fun ω ↦ d (O 0 ω); μ] ≠ 0) :
    IsConsistent (sampleCovRatio z y d O)
      (cov[fun ω ↦ z (O 0 ω), fun ω ↦ y (O 0 ω); μ] /
        cov[fun ω ↦ z (O 0 ω), fun ω ↦ d (O 0 ω); μ]) μ :=
  (sampleCov_isConsistent hO hz hy hz2 hy2).div (sampleCov_isConsistent hO hz hd hz2 hd2) hR

/-- **Consistency of linear IV for the structural slope.** Let the first observation follow the
linear model `L`: `Y = α + β D + U` with `L.Z = z (O 0)`, `L.D = d (O 0)` and the outcome
`L.Y = y (O 0)` (the error `U` need not be observed). Under finite second moments, exogeneity
`Cov(Z, U) = 0` and relevance `Cov(Z, D) ≠ 0`, the sample covariance ratio is consistent for
`β`. -/
theorem sampleCovRatio_isConsistent_beta {μ : Measure Ω} [IsProbabilityMeasure μ]
    {O : ℕ → Ω → 𝒪} (hO : IsIIDSample O μ) {z y d : 𝒪 → ℝ} (hz : Measurable z)
    (hy : Measurable y) (hd : Measurable d) (L : LinearIVModel Ω)
    (hLZ : L.Z = fun ω ↦ z (O 0 ω)) (hLD : L.D = fun ω ↦ d (O 0 ω))
    (hLY : L.Y = fun ω ↦ y (O 0 ω)) (hS : L.SecondMoments μ) (hE : L.Exogeneity μ)
    (hR : L.Relevance μ) :
    IsConsistent (sampleCovRatio z y d O) L.β μ := by
  have hY2 : MemLp L.Y 2 μ := by
    have h : L.Y = fun ω ↦ L.α + (L.β * L.D ω + L.U ω) := by
      funext ω; simp only [LinearIVModel.Y]; ring
    rw [h]
    exact (memLp_const L.α).add ((hS.memLp_D.const_mul L.β).add hS.memLp_U)
  rw [LinearIVModel.beta_eq_covRatio hS hE hR]
  have hR' := hR
  unfold LinearIVModel.Relevance at hR'
  have hz2 := hS.memLp_Z
  have hd2 := hS.memLp_D
  rw [hLZ, hLD] at hR' ⊢
  rw [hLZ] at hz2
  rw [hLD] at hd2
  rw [hLY] at hY2 ⊢
  exact sampleCovRatio_isConsistent hO hz hy hd hz2 hY2 hd2 hR'

/-- The sample mean of `x` among the observations whose binary instrument `zb` equals `b`:
`(∑_{i < n, zb (O i) = b} x (O i)) / #{i < n : zb (O i) = b}`, written as a ratio of two sample
means. It is `0` when no observation has instrument value `b`. -/
noncomputable def sampleCondMean (zb : 𝒪 → Bool) (b : Bool) (x : 𝒪 → ℝ) (O : ℕ → Ω → 𝒪)
    (n : ℕ) (ω : Ω) : ℝ :=
  sampleMean (fun o ↦ if zb o = b then x o else 0) O n ω /
    sampleMean (fun o ↦ if zb o = b then 1 else 0) O n ω

/-- **Consistency of a sample conditional mean.** For an i.i.d. sample under a probability
measure, a measurable binary instrument `zb`, a measurable `x` with `x (O 0)` integrable and an
instrument value `b` of positive probability, the sample mean of `x` in the group `zb = b` is
consistent for the conditional mean `E[x (O 0) | zb (O 0) = b]`. -/
theorem sampleCondMean_isConsistent {μ : Measure Ω} [IsProbabilityMeasure μ] {O : ℕ → Ω → 𝒪}
    (hO : IsIIDSample O μ) {zb : 𝒪 → Bool} (hzb : Measurable zb) (b : Bool) {x : 𝒪 → ℝ}
    (hx : Measurable x) (hint : Integrable (fun ω ↦ x (O 0 ω)) μ)
    (hb : μ ((fun ω ↦ zb (O 0 ω)) ⁻¹' {b}) ≠ 0) :
    IsConsistent (sampleCondMean zb b x O)
      (∫ ω, x (O 0 ω) ∂μ[|(fun ω ↦ zb (O 0 ω)) ⁻¹' {b}]) μ := by
  set S := (fun ω ↦ zb (O 0 ω)) ⁻¹' {b} with hS
  have hSn : NullMeasurableSet S μ :=
    (hzb.comp_aemeasurable (hO.aemeasurable 0)).nullMeasurable (measurableSet_singleton b)
  have hset : MeasurableSet {o | zb o = b} := hzb (measurableSet_singleton b)
  have hmx : Measurable fun o ↦ if zb o = b then x o else 0 := hx.ite hset measurable_const
  have hm1 : Measurable fun o ↦ if zb o = b then (1 : ℝ) else 0 :=
    measurable_const.ite hset measurable_const
  have hix : (fun ω ↦ if zb (O 0 ω) = b then x (O 0 ω) else 0) =
      S.indicator fun ω ↦ x (O 0 ω) := by
    funext ω; by_cases h : zb (O 0 ω) = b <;> simp [S, h]
  have hi1 : (fun ω ↦ if zb (O 0 ω) = b then (1 : ℝ) else 0) = S.indicator 1 := by
    funext ω; by_cases h : zb (O 0 ω) = b <;> simp [S, h]
  have h1 := sampleMean_isConsistent hO hmx (by rw [hix]; exact hint.indicator₀ hSn)
  have h2 := sampleMean_isConsistent hO hm1
    (by rw [hi1]; exact (integrable_const (1 : ℝ)).indicator₀ hSn)
  have hpos : μ.real S ≠ 0 := by
    rw [measureReal_def]
    exact ENNReal.toReal_ne_zero.mpr ⟨hb, measure_ne_top μ S⟩
  have key := h1.div h2 (by
    simp only at hi1 ⊢
    rw [hi1, integral_indicator₀ hSn]
    simpa using hpos)
  rw [hix, hi1, integral_indicator₀ hSn, integral_indicator₀ hSn] at key
  have htarget : (∫ ω in S, x (O 0 ω) ∂μ) / (∫ ω in S, (1 : Ω → ℝ) ω ∂μ) =
      ∫ ω, x (O 0 ω) ∂μ[|S] := by
    simp only [Pi.one_apply]
    rw [setIntegral_const, smul_eq_mul, mul_one, ProbabilityTheory.cond, integral_smul_measure,
      ENNReal.toReal_inv, smul_eq_mul, ← measureReal_def]
    field_simp
  rw [← htarget]
  exact key

/-- The sample Wald ratio for a binary instrument `zb`: the difference between the sample mean
outcomes of the groups `zb = true` and `zb = false`, divided by the corresponding difference in
sample mean treatments. It is `0` when that denominator vanishes. -/
noncomputable def sampleWald (zb : 𝒪 → Bool) (y d : 𝒪 → ℝ) (O : ℕ → Ω → 𝒪) (n : ℕ) (ω : Ω) :
    ℝ :=
  (sampleCondMean zb true y O n ω - sampleCondMean zb false y O n ω) /
    (sampleCondMean zb true d O n ω - sampleCondMean zb false d O n ω)

/-- **Consistency of the sample Wald ratio** (Wald 1940). For an i.i.d. sample under a
probability measure, a measurable binary instrument `zb` whose two values both have positive
probability, measurable `y` and `d` with `y (O 0)` and `d (O 0)` integrable, and a nonzero first
stage `E[D | Z = 1] - E[D | Z = 0] ≠ 0`, the sample Wald ratio is consistent for the population
Wald ratio `(E[Y | Z = 1] - E[Y | Z = 0]) / (E[D | Z = 1] - E[D | Z = 0])`. -/
theorem sampleWald_isConsistent {μ : Measure Ω} [IsProbabilityMeasure μ] {O : ℕ → Ω → 𝒪}
    (hO : IsIIDSample O μ) {zb : 𝒪 → Bool} (hzb : Measurable zb) {y d : 𝒪 → ℝ}
    (hy : Measurable y) (hd : Measurable d) (hyi : Integrable (fun ω ↦ y (O 0 ω)) μ)
    (hdi : Integrable (fun ω ↦ d (O 0 ω)) μ)
    (h₁ : μ ((fun ω ↦ zb (O 0 ω)) ⁻¹' {true}) ≠ 0)
    (h₀ : μ ((fun ω ↦ zb (O 0 ω)) ⁻¹' {false}) ≠ 0)
    (hR : ∫ ω, d (O 0 ω) ∂μ[|(fun ω ↦ zb (O 0 ω)) ⁻¹' {true}] -
      ∫ ω, d (O 0 ω) ∂μ[|(fun ω ↦ zb (O 0 ω)) ⁻¹' {false}] ≠ 0) :
    IsConsistent (sampleWald zb y d O)
      ((∫ ω, y (O 0 ω) ∂μ[|(fun ω ↦ zb (O 0 ω)) ⁻¹' {true}] -
          ∫ ω, y (O 0 ω) ∂μ[|(fun ω ↦ zb (O 0 ω)) ⁻¹' {false}]) /
        (∫ ω, d (O 0 ω) ∂μ[|(fun ω ↦ zb (O 0 ω)) ⁻¹' {true}] -
          ∫ ω, d (O 0 ω) ∂μ[|(fun ω ↦ zb (O 0 ω)) ⁻¹' {false}])) μ :=
  IsConsistent.div
    ((sampleCondMean_isConsistent hO hzb true hy hyi h₁).sub
      (sampleCondMean_isConsistent hO hzb false hy hyi h₀))
    ((sampleCondMean_isConsistent hO hzb true hd hdi h₁).sub
      (sampleCondMean_isConsistent hO hzb false hd hdi h₀)) hR

/-- **The sample Wald ratio estimates the IV covariance ratio.** Under the hypotheses of
`sampleWald_isConsistent`, with the first observation `O 0` measurable, the sample Wald ratio is
consistent for `Cov(Z, Y) / Cov(Z, D)` with the instrument coded as `0`/`1`
(`LinearIV.covRatio_eq_waldRatio`). -/
theorem sampleWald_isConsistent_covRatio {μ : Measure Ω} [IsProbabilityMeasure μ]
    {O : ℕ → Ω → 𝒪} (hO : IsIIDSample O μ) (hO0 : Measurable (O 0)) {zb : 𝒪 → Bool}
    (hzb : Measurable zb) {y d : 𝒪 → ℝ} (hy : Measurable y) (hd : Measurable d)
    (hyi : Integrable (fun ω ↦ y (O 0 ω)) μ) (hdi : Integrable (fun ω ↦ d (O 0 ω)) μ)
    (h₁ : μ ((fun ω ↦ zb (O 0 ω)) ⁻¹' {true}) ≠ 0)
    (h₀ : μ ((fun ω ↦ zb (O 0 ω)) ⁻¹' {false}) ≠ 0)
    (hR : ∫ ω, d (O 0 ω) ∂μ[|(fun ω ↦ zb (O 0 ω)) ⁻¹' {true}] -
      ∫ ω, d (O 0 ω) ∂μ[|(fun ω ↦ zb (O 0 ω)) ⁻¹' {false}] ≠ 0) :
    IsConsistent (sampleWald zb y d O)
      (cov[fun ω ↦ IVModel.boolToReal (zb (O 0 ω)), fun ω ↦ y (O 0 ω); μ] /
        cov[fun ω ↦ IVModel.boolToReal (zb (O 0 ω)), fun ω ↦ d (O 0 ω); μ]) μ := by
  rw [LinearIV.covRatio_eq_waldRatio (Zb := fun ω ↦ zb (O 0 ω)) (hzb.comp hO0) hyi hdi h₁ h₀
    hR]
  exact sampleWald_isConsistent hO hzb hy hd hyi hdi h₁ h₀ hR

/-- **A ratio with a vanishing denominator is not consistent.** If `a` is consistent for
`α ≠ 0` and `b` is consistent for `0`, then `a / b` is consistent for no constant `c`, unless
the probability that `b n ≠ 0` tends to `0` (so that only the convention `x / 0 = 0` could make
the ratio converge, and then only to `0`). This is the failure of the continuous mapping step
`IsConsistent.div` when the limit of the denominator is zero. -/
theorem IsConsistent.not_div_of_tendsto_zero {μ : Measure Ω} {a b : ℕ → Ω → ℝ} {α : ℝ}
    (ha : IsConsistent a α μ) (hα : α ≠ 0) (hb : IsConsistent b 0 μ)
    (hne : ¬ Tendsto (fun n ↦ μ {ω | b n ω ≠ 0}) atTop (𝓝 0)) (c : ℝ) :
    ¬ IsConsistent (fun n ω ↦ a n ω / b n ω) c μ := by
  intro hc
  apply hne
  rw [IsConsistent, tendstoInMeasure_iff_dist] at ha hb hc
  have hαpos : 0 < |α| := abs_pos.2 hα
  set δ := |α| / (2 * (|c| + 1)) with hδ
  have hδpos : 0 < δ := by positivity
  have hcδ : (|c| + 1) * δ = |α| / 2 := by
    rw [hδ]
    field_simp
  have hsum := ((hc 1 one_pos).add (hb δ hδpos)).add (ha (|α| / 2) (by positivity))
  simp only [add_zero] at hsum
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsum (fun _ ↦ zero_le)
    fun n ↦ (measure_mono fun ω hω ↦ ?_).trans ((measure_union_le _ _).trans
      (by gcongr; exact measure_union_le _ _))
  simp only [Set.mem_ofPred_eq, Set.mem_union] at hω ⊢
  by_contra! h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  rw [Real.dist_eq] at h1 h2 h3
  rw [sub_zero] at h2
  have hb0 : 0 < |b n ω| := abs_pos.2 hω
  have ha' : |α| / 2 < |a n ω| := by
    have := abs_sub_abs_le_abs_sub α (a n ω)
    rw [abs_sub_comm] at h3
    linarith
  have hq : |c| + 1 < |a n ω / b n ω| := by
    rw [abs_div, lt_div_iff₀ hb0]
    nlinarith
  have := abs_sub_abs_le_abs_sub (a n ω / b n ω) c
  linarith

/-- The hypotheses of `IsConsistent.not_div_of_tendsto_zero` are jointly satisfiable: on a one
point probability space, `a n = 1` is consistent for `1`, `b n = 1 / (n + 1)` is consistent for
`0`, and `b n ≠ 0` with probability one for every `n`. -/
theorem not_div_of_tendsto_zero_hypotheses_satisfiable :
    ∃ a b : ℕ → Unit → ℝ, IsConsistent a 1 (Measure.dirac ()) ∧
      IsConsistent b 0 (Measure.dirac ()) ∧
      ¬ Tendsto (fun n ↦ Measure.dirac () {ω | b n ω ≠ 0}) atTop (𝓝 0) := by
  refine ⟨fun _ _ ↦ 1, fun n _ ↦ 1 / ((n : ℝ) + 1), ?_, ?_, ?_⟩
  · exact tendstoInMeasure_of_tendsto_ae (fun _ ↦ aestronglyMeasurable_const)
      (ae_of_all _ fun _ ↦ tendsto_const_nhds)
  · exact tendstoInMeasure_of_tendsto_ae (fun _ ↦ aestronglyMeasurable_const)
      (ae_of_all _ fun _ ↦ tendsto_one_div_add_atTop_nhds_zero_nat)
  · have h : ∀ n : ℕ, {ω : Unit | 1 / ((n : ℝ) + 1) ≠ 0} = Set.univ := fun n ↦ by
      ext; simp only [Set.mem_ofPred_eq, Set.mem_univ, iff_true]; positivity
    simp only [h, measure_univ]
    exact fun h1 ↦ one_ne_zero (tendsto_nhds_unique tendsto_const_nhds h1)

/-- **What fails at a zero first stage.** For an i.i.d. sample under a probability measure,
measurable `z`, `y`, `d` with finite second moments, a zero first stage `Cov(Z, D) = 0` and a
nonzero reduced form `Cov(Z, Y) ≠ 0`: unless the sample first stage `Ĉov(Z, D)` is exactly zero
with probability tending to one, the sample covariance ratio is consistent for no constant `c`.
In particular it is not consistent for the population ratio `Cov(Z, Y) / Cov(Z, D)`, which is
`0` only by the convention `x / 0 = 0`. -/
theorem sampleCovRatio_not_isConsistent {μ : Measure Ω} [IsProbabilityMeasure μ]
    {O : ℕ → Ω → 𝒪} (hO : IsIIDSample O μ) {z y d : 𝒪 → ℝ} (hz : Measurable z)
    (hy : Measurable y) (hd : Measurable d) (hz2 : MemLp (fun ω ↦ z (O 0 ω)) 2 μ)
    (hy2 : MemLp (fun ω ↦ y (O 0 ω)) 2 μ) (hd2 : MemLp (fun ω ↦ d (O 0 ω)) 2 μ)
    (hR0 : cov[fun ω ↦ z (O 0 ω), fun ω ↦ d (O 0 ω); μ] = 0)
    (hRF : cov[fun ω ↦ z (O 0 ω), fun ω ↦ y (O 0 ω); μ] ≠ 0)
    (hne : ¬ Tendsto (fun n ↦ μ {ω | sampleCov z d O n ω ≠ 0}) atTop (𝓝 0)) (c : ℝ) :
    ¬ IsConsistent (sampleCovRatio z y d O) c μ := by
  have hb := sampleCov_isConsistent hO hz hd hz2 hd2
  rw [hR0] at hb
  exact (sampleCov_isConsistent hO hz hy hz2 hy2).not_div_of_tendsto_zero hRF hb hne c

end CausalInference
