/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.Estimation.Consistency
public import CausalInference.InstrumentalVariables.LinearIV
public import Mathlib.Probability.Independence.Integration
public import Mathlib.MeasureTheory.Integral.Pi

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
  of the abstract statement can hold together. In the linear model a zero first stage makes the
  reduced form equal to `Cov(Z, U)` (`LinearIVModel.covariance_Z_Y_of_firstStage_eq_zero`), so
  the sampling statement concerns an instrument that is also not exogenous.
* Countermodels on an i.i.d. sample of two fair coins (instrument the first coin, treatment the
  second): `IVConsistencyExample.sampleCovRatio_not_isConsistent_example`, with outcome equal to
  the instrument, satisfies every hypothesis of `CausalInference.sampleCovRatio_not_isConsistent`
  (the sample first stage is nonzero with probability at least `1/4` at every even sample size,
  by a parity argument); `IVConsistencyExample.irrelevant_not_isConsistent` is a linear model
  with finite second moments and an exogenous instrument in which only relevance fails, and the
  sample covariance ratio is not consistent for `β`; there the error equals the treatment.
  `IVConsistencyExample.exists_relevance_only_countermodel` (built on
  `IVConsistencyExample.threeCoins_not_isConsistent`) is a linear model on three independent
  fair coins with an exogenous instrument, an error independent of instrument and treatment and
  a zero first stage, in which the sample covariance ratio is not consistent for `β`: by an
  exchange of treatment and error in every draw, it is at least `1` in absolute value with
  probability at least `1/16` at every even sample size. By a flip of the error in every draw,
  which negates the ratio, it is consistent for no constant at all
  (`IVConsistencyExample.threeCoins_not_isConsistent_const`,
  `IVConsistencyExample.exists_relevance_only_countermodel_const`).

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
`0` only by the convention `x / 0 = 0`. In the linear model `Y = α + β D + U` a zero first stage
makes the reduced form `Cov(Z, Y)` equal to `Cov(Z, U)`
(`LinearIVModel.covariance_Z_Y_of_firstStage_eq_zero`), so the hypotheses describe an instrument
that is both irrelevant and not exogenous; they never hold for an exogenous instrument. A model
in which all the hypotheses hold is `IVConsistencyExample.sampleCovRatio_not_isConsistent_example`;
the failure of relevance alone is `IVConsistencyExample.irrelevant_not_isConsistent` and, with
an error independent of instrument and treatment,
`IVConsistencyExample.exists_relevance_only_countermodel`. -/
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

/-- In the linear model `Y = α + β D + U` with finite second moments, a zero first stage
`Cov(Z, D) = 0` makes the reduced form equal to the covariance of the instrument with the error:
`Cov(Z, Y) = Cov(Z, U)`. So with an exogenous instrument a zero first stage forces a zero reduced
form. -/
theorem LinearIVModel.covariance_Z_Y_of_firstStage_eq_zero {μ : Measure Ω}
    [IsProbabilityMeasure μ] {L : LinearIVModel Ω} (h : L.SecondMoments μ)
    (hR0 : cov[L.Z, L.D; μ] = 0) :
    cov[L.Z, L.Y; μ] = cov[L.Z, L.U; μ] := by
  rw [LinearIVModel.covariance_Y h.memLp_Z h.memLp_D h.memLp_U, hR0, mul_zero, zero_add]

/-! ### Countermodels at a zero first stage -/

namespace IVConsistencyExample

open LinearIVExample IVModel Finset

/-- The instrument of the countermodels: the first of two fair coins, coded `0`/`1`. -/
def coinZ (o : Bool × Bool) : ℝ := boolToReal o.1

/-- The treatment of the countermodels: the second coin, coded `0`/`1`, independent of the
instrument. -/
def coinD (o : Bool × Bool) : ℝ := boolToReal o.2

/-- A parity argument. If the sample size `n` is even and positive, and both the number of
instrument values `1` and the number of treatment values `1` among the first `n` observations
are odd, then the sample covariance of instrument and treatment is not `0`: `n²` times it is
`n a - b c` for counts `a`, `b`, `c` with `b c` odd and `n a` even. -/
theorem sampleCov_ne_zero_of_odd {O : ℕ → Ω → Bool × Bool} {n : ℕ} (hn : Even n)
    (hn0 : n ≠ 0) {ω : Ω} (h1 : Odd (∑ i ∈ range n, (O i ω).1.toNat))
    (h2 : Odd (∑ i ∈ range n, (O i ω).2.toNat)) : sampleCov coinZ coinD O n ω ≠ 0 := by
  intro h
  have hz : ∀ o, coinZ o = (o.1.toNat : ℝ) := by rintro ⟨a, b⟩; cases a <;> simp [coinZ]
  have hd : ∀ o, coinD o = (o.2.toNat : ℝ) := by rintro ⟨a, b⟩; cases b <;> simp [coinD]
  have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hn0
  set A := ∑ i ∈ range n, coinZ (O i ω) * coinD (O i ω)
  set B := ∑ i ∈ range n, coinZ (O i ω)
  set C := ∑ i ∈ range n, coinD (O i ω)
  have h' : (n : ℝ)⁻¹ * A - (n : ℝ)⁻¹ * B * ((n : ℝ)⁻¹ * C) = 0 := h
  have e : (n : ℝ) * A = B * C := by
    have : (n : ℝ) * A = (n : ℝ) ^ 2 * ((n : ℝ)⁻¹ * A - (n : ℝ)⁻¹ * B * ((n : ℝ)⁻¹ * C)) +
        B * C := by field_simp; ring
    rw [this, h']; ring
  simp only [A, B, C, hz, hd] at e
  have e' : n * ∑ i ∈ range n, (O i ω).1.toNat * (O i ω).2.toNat =
      (∑ i ∈ range n, (O i ω).1.toNat) * ∑ i ∈ range n, (O i ω).2.toNat := by
    exact_mod_cast e
  have hodd := h1.mul h2
  rw [← e'] at hodd
  exact (Nat.not_even_iff_odd.2 hodd) (hn.mul_right _)

variable {μ : Measure Ω} [IsProbabilityMeasure μ] {O : ℕ → Ω → Bool × Bool}

omit [IsProbabilityMeasure μ] in
/-- For an i.i.d. sample of two fair coins, the mean of `∏_{i < n} g (O i)` is `0` when `n ≠ 0`
and `g` has mean `0` under the law of one observation. -/
theorem integral_prod_eq_zero (hO : IsIIDSample O μ) (hm : ∀ i, Measurable (O i))
    (hlaw : ∀ i, HasLaw (O i) coins μ) {n : ℕ} (hn : n ≠ 0) {g : Bool × Bool → ℝ}
    (hg : ∫ x, g x ∂coins = 0) : ∫ ω, ∏ i ∈ range n, g (O i ω) ∂μ = 0 := by
  have hgm : AEStronglyMeasurable g coins := (measurable_of_countable g).aestronglyMeasurable
  simp_rw [← Fin.prod_univ_eq_prod_range (fun i ↦ g (O i _)) n]
  have hI : iIndepFun (fun i : Fin n ↦ O i) μ :=
    ProbabilityTheory.iIndepFun.precomp Fin.val_injective hO.indep
  rw [ProbabilityTheory.iIndepFun.integral_fun_prod_comp (f := fun _ ↦ g) hI
    (fun i ↦ (hm i).aemeasurable)
    (fun i ↦ (measurable_of_countable g).aestronglyMeasurable)]
  have h0 : ∀ i : Fin n, ∫ ω, g (O i ω) ∂μ = 0 := fun i ↦ by
    rw [← hg]; exact (hlaw i).integral_comp hgm
  exact Finset.prod_eq_zero (Finset.mem_univ ⟨0, Nat.pos_of_ne_zero hn⟩) (h0 _)

/-- For an i.i.d. sample of two fair coins and `n ≠ 0`, the event that the number of first coins
equal to `1` and the number of second coins equal to `1` among the first `n` observations are
both odd has probability `1/4`. -/
theorem measureReal_odd_odd (hO : IsIIDSample O μ) (hm : ∀ i, Measurable (O i))
    (hlaw : ∀ i, HasLaw (O i) coins μ) {n : ℕ} (hn : n ≠ 0) :
    μ.real {ω | Odd (∑ i ∈ range n, (O i ω).1.toNat) ∧
      Odd (∑ i ∈ range n, (O i ω).2.toNat)} = 1 / 4 := by
  set E := {ω | Odd (∑ i ∈ range n, (O i ω).1.toNat) ∧ Odd (∑ i ∈ range n, (O i ω).2.toNat)}
  have hs : ∀ f : Bool × Bool → ℕ, Measurable fun ω ↦ ∑ i ∈ range n, f (O i ω) := fun f ↦
    Finset.measurable_sum _ fun i _ ↦ (measurable_of_countable f).comp (hm i)
  have hE : MeasurableSet E :=
    ((hs fun o ↦ o.1.toNat).prodMk (hs fun o ↦ o.2.toNat))
      ((Set.to_countable {p : ℕ × ℕ | Odd p.1 ∧ Odd p.2}).measurableSet)
  let g₁ : Bool × Bool → ℝ := fun o ↦ (-1) ^ o.1.toNat
  let g₂ : Bool × Bool → ℝ := fun o ↦ (-1) ^ o.2.toNat
  let P : (Bool × Bool → ℝ) → Ω → ℝ := fun g ω ↦ ∏ i ∈ range n, g (O i ω)
  have hP : ∀ g : Bool × Bool → ℝ, (∀ x, |g x| ≤ 1) → Integrable (P g) μ := fun g hg ↦
    Integrable.of_bound (Finset.measurable_prod _ fun i _ ↦
      (measurable_of_countable g).comp (hm i)).aestronglyMeasurable 1
      (ae_of_all _ fun ω ↦ by
        rw [Real.norm_eq_abs, Finset.abs_prod]
        exact Finset.prod_le_one₀ (fun _ _ ↦ abs_nonneg _) fun _ _ ↦ hg _)
  have hb₁ : ∀ x, |g₁ x| ≤ 1 := fun x ↦ by simp [g₁]
  have hb₂ : ∀ x, |g₂ x| ≤ 1 := fun x ↦ by simp [g₂]
  have hb₁₂ : ∀ x, |g₁ x * g₂ x| ≤ 1 := fun x ↦ by simp [g₁, g₂]
  have hind : E.indicator (1 : Ω → ℝ) =
      fun ω ↦ (1 - P g₁ ω - P g₂ ω + P (fun o ↦ g₁ o * g₂ o) ω) / 4 := by
    funext ω
    simp only [P, Finset.prod_mul_distrib, g₁, g₂, Finset.prod_pow_eq_pow_sum]
    rcases Nat.even_or_odd (∑ i ∈ range n, (O i ω).1.toNat) with ha | ha <;>
      rcases Nat.even_or_odd (∑ i ∈ range n, (O i ω).2.toNat) with hb | hb <;>
      simp [E, ha, hb, ha.neg_one_pow, hb.neg_one_pow, Nat.not_odd_iff_even.2]
    norm_num
  have h0 : ∀ g : Bool × Bool → ℝ, ∫ x, g x ∂coins = 0 → ∫ ω, P g ω ∂μ = 0 := fun g hg ↦
    integral_prod_eq_zero hO hm hlaw hn hg
  have i₁ : ∫ x, g₁ x ∂coins = 0 := by rw [integral_coins]; simp [g₁]
  have i₂ : ∫ x, g₂ x ∂coins = 0 := by rw [integral_coins]; simp [g₂]
  have i₁₂ : ∫ x, g₁ x * g₂ x ∂coins = 0 := by rw [integral_coins]; simp [g₁, g₂]
  rw [← integral_indicator_one hE, hind, integral_div, integral_add, integral_sub, integral_sub,
    integral_const, h0 _ i₁, h0 _ i₂, h0 _ i₁₂]
  · simp
  all_goals first
    | exact integrable_const _
    | exact hP _ hb₁
    | exact hP _ hb₂
    | exact hP _ hb₁₂
    | exact (integrable_const _).sub (hP _ hb₁)
    | exact ((integrable_const _).sub (hP _ hb₁)).sub (hP _ hb₂)

/-- If each event `S n` of an even positive sample size contains the parity event of
`IVConsistencyExample.measureReal_odd_odd`, the probabilities `μ (S n)` do not tend to `0`:
they are at least `1/4` along the even sample sizes. -/
theorem not_tendsto_zero_of_odd (hO : IsIIDSample O μ) (hm : ∀ i, Measurable (O i))
    (hlaw : ∀ i, HasLaw (O i) coins μ) {S : ℕ → Set Ω}
    (hS : ∀ n, Even n → n ≠ 0 → ∀ ω, Odd (∑ i ∈ range n, (O i ω).1.toNat) →
      Odd (∑ i ∈ range n, (O i ω).2.toNat) → ω ∈ S n) :
    ¬ Tendsto (fun n ↦ μ (S n)) atTop (𝓝 0) := by
  intro h
  obtain ⟨N, hN⟩ := eventually_atTop.1 ((tendsto_order.1 h).2 (ENNReal.ofReal (1 / 4))
    (by norm_num))
  have hlt := hN (2 * N + 2) (by omega)
  refine (not_lt.2 ?_) hlt
  rw [← measureReal_odd_odd hO hm hlaw (n := 2 * N + 2) (by omega), ofReal_measureReal]
  exact measure_mono fun ω hω ↦
    hS _ ⟨N + 1, by ring⟩ (by omega) ω hω.1 hω.2

omit [IsProbabilityMeasure μ] in
/-- Covariances of functions of the first observation of a sample with law `coins` are
covariances under `coins`. -/
theorem covariance_comp (hm : ∀ i, Measurable (O i)) (hlaw : ∀ i, HasLaw (O i) coins μ)
    (f g : Bool × Bool → ℝ) :
    cov[fun ω ↦ f (O 0 ω), fun ω ↦ g (O 0 ω); μ] = cov[f, g; coins] := by
  rw [← (hlaw 0).map_eq, covariance_map_fun (measurable_of_countable f).aestronglyMeasurable
    (measurable_of_countable g).aestronglyMeasurable (hm 0).aemeasurable]

omit [IsProbabilityMeasure μ] in
/-- Bounded functions of the first observation of a sample with law `coins` are square
integrable. -/
theorem memLp_comp (hlaw : ∀ i, HasLaw (O i) coins μ) {f : Bool × Bool → ℝ}
    (hf : ∀ x, |f x| ≤ 2) : MemLp (fun ω ↦ f (O 0 ω)) 2 μ :=
  (hlaw 0).memLp_comp (memLp_coins hf)

/-- **The hypotheses of `sampleCovRatio_not_isConsistent` hold together.** Let `O` be an
i.i.d. sample of two fair coins (such a sample exists by `exists_isIIDSample`), the instrument
the first coin, the treatment the second coin and the outcome equal to the instrument. Then
the first stage `Cov(Z, D)` is `0`, the reduced form `Cov(Z, Y) = 1/4` is not, and the
probability that the sample first stage is nonzero does not tend to `0` (it is at least `1/4`
at every even sample size, by a parity argument). So the sample covariance ratio is consistent
for no constant. In the linear model `Y = α + β D + U` this outcome has `U = Z - β D`, so
`Cov(Z, U) ≠ 0`: the instrument is both irrelevant and invalid (see
`LinearIVModel.covariance_Z_Y_of_firstStage_eq_zero`). -/
theorem sampleCovRatio_not_isConsistent_example (hO : IsIIDSample O μ)
    (hm : ∀ i, Measurable (O i)) (hlaw : ∀ i, HasLaw (O i) coins μ) :
    cov[fun ω ↦ coinZ (O 0 ω), fun ω ↦ coinD (O 0 ω); μ] = 0 ∧
      cov[fun ω ↦ coinZ (O 0 ω), fun ω ↦ coinZ (O 0 ω); μ] = 1 / 4 ∧
      ¬ Tendsto (fun n ↦ μ {ω | sampleCov coinZ coinD O n ω ≠ 0}) atTop (𝓝 0) ∧
      ∀ c, ¬ IsConsistent (sampleCovRatio coinZ coinZ coinD O) c μ := by
  have hZD : cov[fun ω ↦ coinZ (O 0 ω), fun ω ↦ coinD (O 0 ω); μ] = 0 := by
    rw [covariance_comp hm hlaw]; simp only [covariance, integral_coins, coinZ, coinD]; norm_num
  have hZZ : cov[fun ω ↦ coinZ (O 0 ω), fun ω ↦ coinZ (O 0 ω); μ] = 1 / 4 := by
    rw [covariance_comp hm hlaw]; simp only [covariance, integral_coins, coinZ]; norm_num
  have hne : ¬ Tendsto (fun n ↦ μ {ω | sampleCov coinZ coinD O n ω ≠ 0}) atTop (𝓝 0) :=
    not_tendsto_zero_of_odd hO hm hlaw fun n hn hn0 ω h1 h2 ↦
      sampleCov_ne_zero_of_odd hn hn0 h1 h2
  have hb : ∀ x, |coinZ x| ≤ 2 := fun ⟨a, _⟩ ↦ by cases a <;> norm_num [coinZ]
  have hb' : ∀ x, |coinD x| ≤ 2 := fun ⟨_, b⟩ ↦ by cases b <;> norm_num [coinD]
  refine ⟨hZD, hZZ, hne, fun c ↦ ?_⟩
  exact sampleCovRatio_not_isConsistent hO (measurable_of_countable _)
    (measurable_of_countable _) (measurable_of_countable _) (memLp_comp hlaw hb)
    (memLp_comp hlaw hb) (memLp_comp hlaw hb') hZD (by rw [hZZ]; norm_num) hne c

/-- The linear model of the relevance countermodel: on an i.i.d. sample `O` of two fair coins,
the first observation has instrument `Z` (the first coin), treatment `D` (the second coin),
structural error `U = D`, and `α = β = 0`, so that `Y = D`. -/
noncomputable def irrelevant (O : ℕ → Ω → Bool × Bool) : LinearIVModel Ω where
  α := 0
  β := 0
  Z ω := coinZ (O 0 ω)
  D ω := coinD (O 0 ω)
  U ω := coinD (O 0 ω)

/-- **Without relevance the sample IV estimator is not consistent for `β`.** In `irrelevant O`,
built on an i.i.d. sample of two fair coins, the linear model has finite second moments and an
exogenous instrument (`Cov(Z, U) = 0`), and only relevance fails (`Cov(Z, D) = 0`). The
observed outcome is `Y = D`. The sample covariance ratio is `1` whenever the sample first
stage is nonzero, which happens with probability at least `1/4` at every even sample size, so
it is not consistent for the structural slope `β = 0`. This countermodel has the error equal to the
treatment; `IVConsistencyExample.threeCoins_not_isConsistent` is the version with an error
independent of instrument and treatment. -/
theorem irrelevant_not_isConsistent (hO : IsIIDSample O μ) (hm : ∀ i, Measurable (O i))
    (hlaw : ∀ i, HasLaw (O i) coins μ) :
    (irrelevant O).SecondMoments μ ∧ (irrelevant O).Exogeneity μ ∧
      ¬ (irrelevant O).Relevance μ ∧ (irrelevant O).Y = (fun ω ↦ coinD (O 0 ω)) ∧
      ¬ IsConsistent (sampleCovRatio coinZ coinD coinD O) (irrelevant O).β μ := by
  have hb : ∀ x, |coinZ x| ≤ 2 := fun ⟨a, _⟩ ↦ by cases a <;> norm_num [coinZ]
  have hb' : ∀ x, |coinD x| ≤ 2 := fun ⟨_, b⟩ ↦ by cases b <;> norm_num [coinD]
  have hZD : cov[fun ω ↦ coinZ (O 0 ω), fun ω ↦ coinD (O 0 ω); μ] = 0 := by
    rw [covariance_comp hm hlaw]; simp only [covariance, integral_coins, coinZ, coinD]; norm_num
  refine ⟨⟨memLp_comp hlaw hb', memLp_comp hlaw hb, memLp_comp hlaw hb'⟩, hZD,
    fun h ↦ h hZD, by funext ω; simp [irrelevant, LinearIVModel.Y], fun hc ↦ ?_⟩
  rw [IsConsistent, tendstoInMeasure_iff_dist] at hc
  refine not_tendsto_zero_of_odd hO hm hlaw (S := fun n ↦ {ω | (1 / 2 : ℝ) ≤
    dist (sampleCovRatio coinZ coinD coinD O n ω) (irrelevant O).β}) ?_ (hc (1 / 2) (by norm_num))
  intro n hn hn0 ω h1 h2
  have h := sampleCov_ne_zero_of_odd hn hn0 h1 h2
  simp only [Set.mem_ofPred_eq, sampleCovRatio, div_self h, irrelevant, Real.dist_eq]
  norm_num

/-- The countermodels are not vacuous: an i.i.d. sample of two fair coins, with measurable
observations, exists (`exists_isIIDSample`), so `sampleCovRatio_not_isConsistent_example` and
`irrelevant_not_isConsistent` apply to it. -/
theorem exists_coins_sample :
    ∃ Ω : Type, ∃ _ : MeasurableSpace Ω, ∃ P : Measure Ω, ∃ O : ℕ → Ω → Bool × Bool,
      IsProbabilityMeasure P ∧ (∀ i, Measurable (O i)) ∧ IsIIDSample O P ∧
        ∀ i, HasLaw (O i) coins P :=
  exists_isIIDSample coins

/-! ### Only relevance fails, with an independent error -/

/-- Three independent fair coins: the uniform law on `(Bool × Bool) × Bool`, as the product of
the law of two fair coins with that of a third. -/
noncomputable def coins3 : Measure ((Bool × Bool) × Bool) :=
  coins.prod (uniformOn (Set.univ : Set Bool))

instance : IsProbabilityMeasure coins3 := by unfold coins3; infer_instance

theorem coins3_singleton (x : (Bool × Bool) × Bool) : coins3 {x} = 8⁻¹ := by
  obtain ⟨⟨a, b⟩, c⟩ := x
  rw [coins3, ← Set.singleton_prod_singleton, Measure.prod_prod, coins, ←
    Set.singleton_prod_singleton, uniformOn_univ, uniformOn_univ]
  simp only [Set.singleton_prod_singleton, MeasurableSet.singleton, Measure.count_singleton',
    Fintype.card_prod, Fintype.card_bool, Nat.reduceMul, Nat.cast_ofNat, one_div,
    MeasurableSpace.measurableSet_top]
  rw [← ENNReal.mul_inv (by simp) (by simp)]
  norm_num

theorem integral_coins3 (f : (Bool × Bool) × Bool → ℝ) :
    ∫ x, f x ∂coins3 = (∑ x, f x) / 8 := by
  rw [integral_fintype .of_finite]
  simp only [measureReal_def, coins3_singleton, smul_eq_mul]
  rw [← Finset.mul_sum, ENNReal.toReal_inv]
  norm_num
  ring

/-- The instrument of the three-coin model: the first coin, coded `0`/`1`. -/
def zc (o : (Bool × Bool) × Bool) : ℝ := boolToReal o.1.1

/-- The treatment of the three-coin model: the second coin. -/
def dc (o : (Bool × Bool) × Bool) : ℝ := boolToReal o.1.2

/-- The structural error, and outcome, of the three-coin model: the third coin. -/
def uc (o : (Bool × Bool) × Bool) : ℝ := boolToReal o.2

/-- The plug-in covariance of `f` and `g` over a vector of `n` observations. -/
noncomputable def vcov {𝒳 : Type*} {n : ℕ} (f g : 𝒳 → ℝ) (x : Fin n → 𝒳) : ℝ :=
  (n : ℝ)⁻¹ * ∑ i, f (x i) * g (x i) - ((n : ℝ)⁻¹ * ∑ i, f (x i)) * ((n : ℝ)⁻¹ * ∑ i, g (x i))

theorem sampleCov_eq_vcov {𝒳 : Type*} [MeasurableSpace 𝒳] (f g : 𝒳 → ℝ) (X : ℕ → Ω → 𝒳)
    (n : ℕ) (ω : Ω) : sampleCov f g X n ω = vcov f g (fun i : Fin n ↦ X i ω) := by
  simp [sampleCov, sampleMean, vcov, Finset.sum_range]

/-- The exchange of treatment and error, `((z, d), u) ↦ ((z, u), d)`. -/
def swapDU (o : (Bool × Bool) × Bool) : (Bool × Bool) × Bool := ((o.1.1, o.2), o.1.2)

theorem measurePreserving_swapDU : MeasurePreserving swapDU coins3 coins3 := by
  refine ⟨measurable_of_countable _, Measure.ext_of_singleton fun x ↦ ?_⟩
  rw [Measure.map_apply (measurable_of_countable _) (measurableSet_singleton _)]
  have h : swapDU ⁻¹' {x} = {swapDU x} := by
    ext ⟨⟨a, b⟩, c⟩
    simp only [Set.mem_preimage, Set.mem_singleton_iff, swapDU, Prod.ext_iff]
    tauto
  rw [h, coins3_singleton, coins3_singleton]

/-- `n` independent draws of three fair coins. -/
noncomputable abbrev piCoins3 (n : ℕ) : Measure (Fin n → (Bool × Bool) × Bool) :=
  Measure.pi fun _ ↦ coins3

/-- The parity event: the numbers of `1` values of the three coins are all odd. -/
def oddEvent (n : ℕ) : Set (Fin n → (Bool × Bool) × Bool) :=
  {x | Odd (∑ i, (x i).1.1.toNat) ∧ Odd (∑ i, (x i).1.2.toNat) ∧ Odd (∑ i, (x i).2.toNat)}

theorem integral_prod_piCoins3 {n : ℕ} (hn : n ≠ 0) {g : (Bool × Bool) × Bool → ℝ}
    (hg : ∫ x, g x ∂coins3 = 0) : ∫ x, ∏ i, g (x i) ∂piCoins3 n = 0 := by
  rw [integral_fintype_prod_eq_prod (fun _ ↦ g), hg]
  exact Finset.prod_eq_zero (Finset.mem_univ ⟨0, Nat.pos_of_ne_zero hn⟩) rfl

theorem measureReal_oddEvent {n : ℕ} (hn : n ≠ 0) : (piCoins3 n).real (oddEvent n) = 1 / 8 := by
  let P : ((Bool × Bool) × Bool → ℝ) → (Fin n → (Bool × Bool) × Bool) → ℝ :=
    fun g x ↦ ∏ i, g (x i)
  let ga : (Bool × Bool) × Bool → ℝ := fun o ↦ (-1) ^ o.1.1.toNat
  let gb : (Bool × Bool) × Bool → ℝ := fun o ↦ (-1) ^ o.1.2.toNat
  let gc : (Bool × Bool) × Bool → ℝ := fun o ↦ (-1) ^ o.2.toNat
  have hF : MeasurableSet (oddEvent n) := (Set.to_countable _).measurableSet
  have key : (oddEvent n).indicator (1 : (Fin n → (Bool × Bool) × Bool) → ℝ) = fun x ↦
      (1 - P ga x - P gb x - P gc x + P (fun o ↦ ga o * gb o) x + P (fun o ↦ ga o * gc o) x +
        P (fun o ↦ gb o * gc o) x - P (fun o ↦ ga o * gb o * gc o) x) / 8 := by
    funext x
    simp only [P, Finset.prod_mul_distrib, ga, gb, gc, Finset.prod_pow_eq_pow_sum]
    rcases Nat.even_or_odd (∑ i, (x i).1.1.toNat) with ha | ha <;>
      rcases Nat.even_or_odd (∑ i, (x i).1.2.toNat) with hb | hb <;>
      rcases Nat.even_or_odd (∑ i, (x i).2.toNat) with hc | hc <;>
      simp [oddEvent, ha, hb, hc, ha.neg_one_pow, hb.neg_one_pow, hc.neg_one_pow,
        Nat.not_odd_iff_even.2]
    norm_num
  have h0 : ∀ g : (Bool × Bool) × Bool → ℝ, ∫ x, g x ∂coins3 = 0 →
      ∫ x, P g x ∂piCoins3 n = 0 := fun g hg ↦ integral_prod_piCoins3 hn hg
  have m : ∀ g : (Bool × Bool) × Bool → ℝ, (∑ x, g x = 0) → ∫ x, g x ∂coins3 = 0 :=
    fun g hg ↦ by rw [integral_coins3, hg, zero_div]
  rw [← integral_indicator_one hF, key, integral_div, integral_sub, integral_add, integral_add,
    integral_add, integral_sub, integral_sub, integral_sub, integral_const,
    h0 ga (m _ (by simp [ga, Fintype.sum_prod_type])),
    h0 gb (m _ (by simp [gb, Fintype.sum_prod_type])),
    h0 gc (m _ (by simp [gc, Fintype.sum_prod_type])),
    h0 (fun o ↦ ga o * gb o) (m _ (by simp [ga, gb, Fintype.sum_prod_type])),
    h0 (fun o ↦ ga o * gc o) (m _ (by simp [ga, gc, Fintype.sum_prod_type])),
    h0 (fun o ↦ gb o * gc o) (m _ (by simp [gb, gc, Fintype.sum_prod_type])),
    h0 (fun o ↦ ga o * gb o * gc o) (m _ (by simp [ga, gb, gc, Fintype.sum_prod_type]))]
  · simp
  all_goals exact .of_finite

/-- The event that the sample IV estimate `Ĉov(Z, U) / Ĉov(Z, D)` of a vector of draws is at
least `1` in absolute value. -/
def bigRatio (n : ℕ) : Set (Fin n → (Bool × Bool) × Bool) :=
  {x | 1 ≤ |vcov zc uc x / vcov zc dc x|}

/-- The event `|Ĉov(Z, D)| ≤ |Ĉov(Z, U)|` on a vector of draws. -/
def dLeU (n : ℕ) : Set (Fin n → (Bool × Bool) × Bool) := {x | |vcov zc dc x| ≤ |vcov zc uc x|}

/-- The event `|Ĉov(Z, U)| ≤ |Ĉov(Z, D)|` on a vector of draws. -/
def uLeD (n : ℕ) : Set (Fin n → (Bool × Bool) × Bool) := {x | |vcov zc uc x| ≤ |vcov zc dc x|}

/-- The parity argument on a vector of draws: if `n` is even and positive and the numbers of
instrument values `1` and of treatment values `1` among the `n` draws are odd, the plug-in
covariance of instrument and treatment is not `0`. -/
theorem vcov_zd_ne_zero {n : ℕ} (hn : Even n) (hn0 : n ≠ 0) {x : Fin n → (Bool × Bool) × Bool}
    (hx : x ∈ oddEvent n) : vcov zc dc x ≠ 0 := by
  obtain ⟨h1, h2, -⟩ := hx
  intro h
  have hz : ∀ o, zc o = (o.1.1.toNat : ℝ) := by rintro ⟨⟨a, b⟩, c⟩; cases a <;> simp [zc]
  have hd : ∀ o, dc o = (o.1.2.toNat : ℝ) := by rintro ⟨⟨a, b⟩, c⟩; cases b <;> simp [dc]
  have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hn0
  set A := ∑ i, zc (x i) * dc (x i)
  set B := ∑ i, zc (x i)
  set C := ∑ i, dc (x i)
  have h' : (n : ℝ)⁻¹ * A - (n : ℝ)⁻¹ * B * ((n : ℝ)⁻¹ * C) = 0 := h
  have e : (n : ℝ) * A = B * C := by
    have : (n : ℝ) * A = (n : ℝ) ^ 2 * ((n : ℝ)⁻¹ * A - (n : ℝ)⁻¹ * B * ((n : ℝ)⁻¹ * C)) +
        B * C := by field_simp; ring
    rw [this, h']; ring
  simp only [A, B, C, hz, hd] at e
  have e' : n * ∑ i, (x i).1.1.toNat * (x i).1.2.toNat =
      (∑ i, (x i).1.1.toNat) * ∑ i, (x i).1.2.toNat := by
    exact_mod_cast e
  have hodd := h1.mul h2
  rw [← e'] at hodd
  exact (Nat.not_even_iff_odd.2 hodd) (hn.mul_right _)

theorem preimage_swap_oddEvent_inter (n : ℕ) :
    (fun x (i : Fin n) ↦ swapDU (x i)) ⁻¹' (oddEvent n ∩ dLeU n) = oddEvent n ∩ uLeD n := by
  ext x
  change (Odd (∑ i, (x i).1.1.toNat) ∧ Odd (∑ i, (x i).2.toNat) ∧
      Odd (∑ i, (x i).1.2.toNat)) ∧ |vcov zc uc x| ≤ |vcov zc dc x| ↔
    (Odd (∑ i, (x i).1.1.toNat) ∧ Odd (∑ i, (x i).1.2.toNat) ∧
      Odd (∑ i, (x i).2.toNat)) ∧ |vcov zc uc x| ≤ |vcov zc dc x|
  constructor
  · rintro ⟨⟨a, b, c⟩, d⟩; exact ⟨⟨a, c, b⟩, d⟩
  · rintro ⟨⟨a, b, c⟩, d⟩; exact ⟨⟨a, c, b⟩, d⟩

/-- **The exchange argument.** For an even positive number `n` of draws of three fair coins, the
sample covariance ratio `Ĉov(Z, U) / Ĉov(Z, D)` is at least `1` in absolute value with
probability at least `1/16`. On the parity event (probability `1/8`) both sample covariances
are nonzero; the exchange of treatment and error in every draw preserves the law and the parity
event and exchanges the two covariances, so `|Ĉov(Z, D)| ≤ |Ĉov(Z, U)|` holds on at least half
of the parity event. -/
theorem measureReal_bigRatio {n : ℕ} (hn : Even n) (hn0 : n ≠ 0) :
    1 / 16 ≤ (piCoins3 n).real (bigRatio n) := by
  have hsw : MeasurePreserving (fun x (i : Fin n) ↦ swapDU (x i)) (piCoins3 n) (piCoins3 n) :=
    measurePreserving_pi _ _ fun _ ↦ measurePreserving_swapDU
  have heq : (piCoins3 n).real (oddEvent n ∩ dLeU n) = (piCoins3 n).real (oddEvent n ∩ uLeD n) := by
    rw [measureReal_def, measureReal_def, ← preimage_swap_oddEvent_inter,
      hsw.measure_preimage (Set.to_countable _).measurableSet.nullMeasurableSet]
  have hcover : oddEvent n ⊆ (oddEvent n ∩ dLeU n) ∪ (oddEvent n ∩ uLeD n) := fun x hx ↦ by
    rcases le_total |vcov zc dc x| |vcov zc uc x| with h | h
    · exact Or.inl ⟨hx, h⟩
    · exact Or.inr ⟨hx, h⟩
  have hF := measureReal_oddEvent hn0
  have h1 := (measureReal_mono (μ := piCoins3 n) hcover).trans
    (measureReal_union_le (μ := piCoins3 n) (oddEvent n ∩ dLeU n) (oddEvent n ∩ uLeD n))
  have hsub : oddEvent n ∩ dLeU n ⊆ bigRatio n := fun x hx ↦ by
    have hb := vcov_zd_ne_zero hn hn0 hx.1
    have h2 : |vcov zc dc x| ≤ |vcov zc uc x| := hx.2
    change 1 ≤ |vcov zc uc x / vcov zc dc x|
    rw [abs_div, le_div_iff₀ (abs_pos.2 hb), one_mul]
    exact h2
  have h3 := measureReal_mono (μ := piCoins3 n) hsub
  linarith

section Sample

variable {X : ℕ → Ω → (Bool × Bool) × Bool}

omit [IsProbabilityMeasure μ] in
/-- The first `n` draws of an i.i.d. sample of three fair coins have the product law. -/
theorem map_sample_eq_piCoins3 (hX : IsIIDSample X μ) (hm : ∀ i, Measurable (X i))
    (hlaw : ∀ i, HasLaw (X i) coins3 μ) (n : ℕ) :
    μ.map (fun ω (i : Fin n) ↦ X i ω) = piCoins3 n := by
  have hI : iIndepFun (fun i : Fin n ↦ X i) μ :=
    ProbabilityTheory.iIndepFun.precomp Fin.val_injective hX.indep
  rw [ProbabilityTheory.iIndepFun.map_fun_eq_pi_map (fun i : Fin n ↦ (hm i).aemeasurable) hI]
  simp_rw [(hlaw _).map_eq]

/-- The linear model of the three-coin countermodel: the first observation has instrument `Z`
(the first coin), treatment `D` (the second coin) and structural error `U` (the third coin),
with `α = β = 0`, so that `Y = U`. -/
noncomputable def threeCoins (X : ℕ → Ω → (Bool × Bool) × Bool) : LinearIVModel Ω where
  α := 0
  β := 0
  Z ω := zc (X 0 ω)
  D ω := dc (X 0 ω)
  U ω := uc (X 0 ω)

omit [IsProbabilityMeasure μ] in
theorem covariance_comp3 (hm : ∀ i, Measurable (X i)) (hlaw : ∀ i, HasLaw (X i) coins3 μ)
    (f g : (Bool × Bool) × Bool → ℝ) :
    cov[fun ω ↦ f (X 0 ω), fun ω ↦ g (X 0 ω); μ] = cov[f, g; coins3] := by
  rw [← (hlaw 0).map_eq, covariance_map_fun (measurable_of_countable f).aestronglyMeasurable
    (measurable_of_countable g).aestronglyMeasurable (hm 0).aemeasurable]

omit [IsProbabilityMeasure μ] in
theorem memLp_comp3 (hlaw : ∀ i, HasLaw (X i) coins3 μ) (p : (Bool × Bool) × Bool → Bool) :
    MemLp (fun ω ↦ boolToReal (p (X 0 ω))) 2 μ :=
  (hlaw 0).memLp_comp (f := fun x ↦ boolToReal (p x))
    (MemLp.of_bound (measurable_of_countable _).aestronglyMeasurable 1
      (ae_of_all _ fun x ↦ by cases p x <;> simp))

/-- **Without relevance the sample IV estimator is not consistent for `β`, with an independent
error.** On an i.i.d. sample of three fair coins, `threeCoins X` is a linear model with finite
second moments, an exogenous instrument (`Cov(Z, U) = 0`), an error independent of the pair of
instrument and treatment, and a zero first stage `Cov(Z, D) = 0`; the outcome is `Y = U` and the
structural slope is `β = 0`. The sample covariance ratio is not consistent for `β`: at every
even sample size it is at least `1` in absolute value with probability at least `1/16`
(`IVConsistencyExample.measureReal_bigRatio`). It is consistent for no other constant either
(`IVConsistencyExample.threeCoins_not_isConsistent_const`). -/
theorem threeCoins_not_isConsistent (hX : IsIIDSample X μ) (hm : ∀ i, Measurable (X i))
    (hlaw : ∀ i, HasLaw (X i) coins3 μ) :
    (threeCoins X).SecondMoments μ ∧ (threeCoins X).Exogeneity μ ∧
      IndepFun (fun ω ↦ ((threeCoins X).Z ω, (threeCoins X).D ω)) (threeCoins X).U μ ∧
      cov[(threeCoins X).Z, (threeCoins X).D; μ] = 0 ∧
      (threeCoins X).Y = (fun ω ↦ uc (X 0 ω)) ∧ (threeCoins X).β = 0 ∧
      ¬ IsConsistent (sampleCovRatio zc uc dc X) (threeCoins X).β μ := by
  have hZU : cov[(threeCoins X).Z, (threeCoins X).U; μ] = 0 := by
    change cov[fun ω ↦ zc (X 0 ω), fun ω ↦ uc (X 0 ω); μ] = 0
    rw [covariance_comp3 hm hlaw]
    simp only [covariance, integral_coins3, Fintype.sum_prod_type, Fintype.sum_bool, zc, uc]
    norm_num
  have hZD : cov[(threeCoins X).Z, (threeCoins X).D; μ] = 0 := by
    change cov[fun ω ↦ zc (X 0 ω), fun ω ↦ dc (X 0 ω); μ] = 0
    rw [covariance_comp3 hm hlaw]
    simp only [covariance, integral_coins3, Fintype.sum_prod_type, Fintype.sum_bool, zc, dc]
    norm_num
  have hind : IndepFun (fun ω ↦ ((threeCoins X).Z ω, (threeCoins X).D ω)) (threeCoins X).U μ := by
    have hν : IndepFun (fun x : (Bool × Bool) × Bool ↦ (zc x, dc x)) uc coins3 :=
      indepFun_prod (μ := coins) (ν := uniformOn (Set.univ : Set Bool))
        (X := fun p : Bool × Bool ↦ (boolToReal p.1, boolToReal p.2)) (Y := boolToReal)
        (measurable_of_countable _) (measurable_of_countable _)
    have hmap : ∀ {β : Type} [MeasurableSpace β] (h : (Bool × Bool) × Bool → β),
        Measurable h → μ.map (fun ω ↦ h (X 0 ω)) = coins3.map h := fun h hh ↦ by
      rw [← (hlaw 0).map_eq, Measure.map_map hh (hm 0)]; rfl
    rw [indepFun_iff_map_prod_eq_prod_map_map (measurable_of_countable _).aemeasurable
      (measurable_of_countable _).aemeasurable] at hν
    refine (indepFun_iff_map_prod_eq_prod_map_map
      (f := fun ω ↦ ((threeCoins X).Z ω, (threeCoins X).D ω)) (g := (threeCoins X).U)
      ((measurable_of_countable (fun x : (Bool × Bool) × Bool ↦ (zc x, dc x))).comp
        (hm 0)).aemeasurable ((measurable_of_countable uc).comp (hm 0)).aemeasurable).2 ?_
    have e₁ : μ.map (fun ω ↦ (((threeCoins X).Z ω, (threeCoins X).D ω), (threeCoins X).U ω)) =
        coins3.map (fun x ↦ ((zc x, dc x), uc x)) :=
      hmap (fun x ↦ ((zc x, dc x), uc x)) (measurable_of_countable _)
    have e₂ : μ.map (fun ω ↦ ((threeCoins X).Z ω, (threeCoins X).D ω)) =
        coins3.map (fun x ↦ (zc x, dc x)) :=
      hmap (fun x ↦ (zc x, dc x)) (measurable_of_countable _)
    have e₃ : μ.map (threeCoins X).U = coins3.map uc := hmap uc (measurable_of_countable _)
    rw [e₁, e₂, e₃]
    exact hν
  refine ⟨⟨memLp_comp3 hlaw (fun o ↦ o.1.2), memLp_comp3 hlaw (fun o ↦ o.1.1),
    memLp_comp3 hlaw (fun o ↦ o.2)⟩, hZU, hind, hZD,
    by funext ω; simp [threeCoins, LinearIVModel.Y], rfl, fun hc ↦ ?_⟩
  rw [IsConsistent, tendstoInMeasure_iff_dist] at hc
  obtain ⟨N, hN⟩ := eventually_atTop.1 ((tendsto_order.1 (hc 1 one_pos)).2
    (ENNReal.ofReal (1 / 16)) (by norm_num))
  have hlt := hN (2 * N + 2) (by omega)
  refine (not_lt.2 ?_) hlt
  have hset : {ω | (1 : ℝ) ≤ dist (sampleCovRatio zc uc dc X (2 * N + 2) ω) (threeCoins X).β} =
      (fun ω (i : Fin (2 * N + 2)) ↦ X i ω) ⁻¹' bigRatio (2 * N + 2) := by
    ext ω
    simp [sampleCovRatio, sampleCov_eq_vcov, bigRatio, threeCoins, abs_div]
  rw [hset, ← Measure.map_apply (Measurable.of_eval fun i : Fin (2 * N + 2) ↦ hm i)
    (Set.to_countable _).measurableSet, map_sample_eq_piCoins3 hX hm hlaw,
    ← ofReal_measureReal]
  exact ENNReal.ofReal_le_ofReal (measureReal_bigRatio ⟨N + 1, by ring⟩ (by omega))

/-- The flip of the error in a draw, `((z, d), u) ↦ ((z, d), ¬u)`, which codes `U ↦ 1 - U`. -/
def flipU (o : (Bool × Bool) × Bool) : (Bool × Bool) × Bool := (o.1, !o.2)

theorem measurePreserving_flipU : MeasurePreserving flipU coins3 coins3 := by
  refine ⟨measurable_of_countable _, Measure.ext_of_singleton fun x ↦ ?_⟩
  rw [Measure.map_apply (measurable_of_countable _) (measurableSet_singleton _)]
  have h : flipU ⁻¹' {x} = {flipU x} := by
    ext ⟨⟨a, b⟩, c⟩
    obtain ⟨⟨a', b'⟩, c'⟩ := x
    cases c <;> cases c' <;> simp [flipU]
  rw [h, coins3_singleton, coins3_singleton]

/-- The flip of the error negates the plug-in covariance of instrument and error. -/
theorem vcov_flipU {n : ℕ} (x : Fin n → (Bool × Bool) × Bool) :
    vcov zc uc (fun i ↦ flipU (x i)) = -vcov zc uc x := by
  have hu : ∀ o, uc (flipU o) = 1 - uc o := by
    rintro ⟨⟨a, b⟩, c⟩; cases c <;> simp [uc, flipU]
  have hz : ∀ o, zc (flipU o) = zc o := fun _ ↦ rfl
  simp only [vcov, hu, hz, mul_sub, mul_one, Finset.sum_sub_distrib, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  · have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hn
    field_simp
    ring

/-- The flip of the error preserves the law of the draws and turns the event
`ε ≤ |R - c|` for the ratio `R = Ĉov(Z, U) / Ĉov(Z, D)` into `ε ≤ |R + c|`. -/
theorem piCoins3_flip_dist (n : ℕ) (c ε : ℝ) :
    piCoins3 n {x | ε ≤ |vcov zc uc x / vcov zc dc x - c|} =
      piCoins3 n {x | ε ≤ |vcov zc uc x / vcov zc dc x - -c|} := by
  have hfl : MeasurePreserving (fun x (i : Fin n) ↦ flipU (x i)) (piCoins3 n) (piCoins3 n) :=
    measurePreserving_pi _ _ fun _ ↦ measurePreserving_flipU
  have hpre : (fun x (i : Fin n) ↦ flipU (x i)) ⁻¹'
      {x | ε ≤ |vcov zc uc x / vcov zc dc x - -c|} =
      {x | ε ≤ |vcov zc uc x / vcov zc dc x - c|} := by
    ext x
    have hd : vcov zc dc (fun i ↦ flipU (x i)) = vcov zc dc x := rfl
    simp only [Set.mem_preimage, Set.mem_ofPred_eq, vcov_flipU, hd]
    rw [neg_div, sub_neg_eq_add, ← abs_neg]
    ring_nf
  rw [← hpre, hfl.measure_preimage (Set.to_countable _).measurableSet.nullMeasurableSet]

omit [IsProbabilityMeasure μ] in
theorem measure_dist_sampleCovRatio (hX : IsIIDSample X μ) (hm : ∀ i, Measurable (X i))
    (hlaw : ∀ i, HasLaw (X i) coins3 μ) (n : ℕ) (c ε : ℝ) :
    μ {ω | ε ≤ dist (sampleCovRatio zc uc dc X n ω) c} =
      piCoins3 n {x | ε ≤ |vcov zc uc x / vcov zc dc x - c|} := by
  have hset : {ω | ε ≤ dist (sampleCovRatio zc uc dc X n ω) c} =
      (fun ω (i : Fin n) ↦ X i ω) ⁻¹' {x | ε ≤ |vcov zc uc x / vcov zc dc x - c|} := by
    ext ω
    simp [sampleCovRatio, sampleCov_eq_vcov, Real.dist_eq]
  rw [hset, ← Measure.map_apply (Measurable.of_eval fun i : Fin n ↦ hm i)
    (Set.to_countable _).measurableSet, map_sample_eq_piCoins3 hX hm hlaw]

/-- **The sample IV estimator of the three-coin model is consistent for no constant.** On an
i.i.d. sample of three fair coins, where only relevance fails, the sample covariance ratio
`Ĉov(Z, U) / Ĉov(Z, D)` is consistent for no `c`. The flip of the error in every draw preserves
the law of the sample and negates the ratio, so consistency for `c` would give consistency for
`-c`; the two limits force `c = 0`, which `threeCoins_not_isConsistent` excludes. -/
theorem threeCoins_not_isConsistent_const (hX : IsIIDSample X μ) (hm : ∀ i, Measurable (X i))
    (hlaw : ∀ i, HasLaw (X i) coins3 μ) (c : ℝ) :
    ¬ IsConsistent (sampleCovRatio zc uc dc X) c μ := by
  intro hc
  rcases eq_or_ne c 0 with rfl | h0
  · exact (threeCoins_not_isConsistent hX hm hlaw).2.2.2.2.2.2 hc
  have hpos : 0 < |c| := abs_pos.2 h0
  rw [IsConsistent, tendstoInMeasure_iff_dist] at hc
  have h1 := hc |c| hpos
  have h2 : Tendsto (fun n ↦ μ {ω | |c| ≤ dist (sampleCovRatio zc uc dc X n ω) (-c)}) atTop
      (𝓝 0) := by
    refine h1.congr fun n ↦ ?_
    rw [measure_dist_sampleCovRatio hX hm hlaw, measure_dist_sampleCovRatio hX hm hlaw,
      piCoins3_flip_dist]
  have hcov : ∀ n, (1 : ℝ≥0∞) ≤ μ {ω | |c| ≤ dist (sampleCovRatio zc uc dc X n ω) c} +
      μ {ω | |c| ≤ dist (sampleCovRatio zc uc dc X n ω) (-c)} := fun n ↦ by
    refine (measure_univ (μ := μ)).symm.le.trans ((measure_mono fun ω _ ↦ ?_).trans
      (measure_union_le _ _))
    simp only [Set.mem_union, Set.mem_ofPred_eq, Real.dist_eq]
    by_contra! h
    have := abs_add_le (c - sampleCovRatio zc uc dc X n ω) (sampleCovRatio zc uc dc X n ω - -c)
    rw [abs_sub_comm] at h
    have e : c - sampleCovRatio zc uc dc X n ω + (sampleCovRatio zc uc dc X n ω - -c) = 2 * c := by
      ring
    rw [e, abs_mul, abs_two] at this
    linarith [h.1, h.2]
  have hsum := h1.add h2
  rw [add_zero] at hsum
  have := ge_of_tendsto' hsum hcov
  simp at this

end Sample

/-- **A countermodel in which only relevance fails.** There is a linear instrumental variable
model `Y = α + β D + U` with finite second moments, an exogenous instrument, an error independent
of the treatment and of the instrument, and a zero first stage, together with an i.i.d. sample
whose first observation carries it, such that the sample covariance ratio is not consistent for
the true slope `β`. The model is `threeCoins` on an i.i.d. sample of three fair coins; for
non-consistency for every constant see `exists_relevance_only_countermodel_const`. -/
theorem exists_relevance_only_countermodel :
    ∃ Ω : Type, ∃ _ : MeasurableSpace Ω, ∃ μ : Measure Ω,
      ∃ X : ℕ → Ω → (Bool × Bool) × Bool, ∃ L : LinearIVModel Ω,
        IsProbabilityMeasure μ ∧ IsIIDSample X μ ∧ L.Z = (fun ω ↦ zc (X 0 ω)) ∧
        L.D = (fun ω ↦ dc (X 0 ω)) ∧ L.Y = (fun ω ↦ uc (X 0 ω)) ∧ L.SecondMoments μ ∧
        L.Exogeneity μ ∧ IndepFun (fun ω ↦ (L.Z ω, L.D ω)) L.U μ ∧ cov[L.Z, L.D; μ] = 0 ∧
        ¬ IsConsistent (sampleCovRatio zc uc dc X) L.β μ := by
  obtain ⟨Ω, _, μ, X, hμ, hm, hX, hlaw⟩ := exists_isIIDSample coins3
  obtain ⟨h1, h2, h3, h4, h5, -, h7⟩ := threeCoins_not_isConsistent hX hm hlaw
  exact ⟨Ω, _, μ, X, threeCoins X, hμ, hX, rfl, rfl, h5, h1, h2, h3, h4, h7⟩

/-- **A countermodel in which only relevance fails, for every constant.** There is a linear
instrumental variable model with finite second moments, an exogenous instrument, an error
independent of the treatment and of the instrument, and a zero first stage, together with an
i.i.d. sample whose first observation carries it, such that the sample covariance ratio is
consistent for no constant `c`, the true slope `β` included. -/
theorem exists_relevance_only_countermodel_const :
    ∃ Ω : Type, ∃ _ : MeasurableSpace Ω, ∃ μ : Measure Ω,
      ∃ X : ℕ → Ω → (Bool × Bool) × Bool, ∃ L : LinearIVModel Ω,
        IsProbabilityMeasure μ ∧ IsIIDSample X μ ∧ L.Z = (fun ω ↦ zc (X 0 ω)) ∧
        L.D = (fun ω ↦ dc (X 0 ω)) ∧ L.Y = (fun ω ↦ uc (X 0 ω)) ∧ L.SecondMoments μ ∧
        L.Exogeneity μ ∧ IndepFun (fun ω ↦ (L.Z ω, L.D ω)) L.U μ ∧ cov[L.Z, L.D; μ] = 0 ∧
        ∀ c, ¬ IsConsistent (sampleCovRatio zc uc dc X) c μ := by
  obtain ⟨Ω, _, μ, X, hμ, hm, hX, hlaw⟩ := exists_isIIDSample coins3
  obtain ⟨h1, h2, h3, h4, h5, -, -⟩ := threeCoins_not_isConsistent hX hm hlaw
  exact ⟨Ω, _, μ, X, threeCoins X, hμ, hX, rfl, rfl, h5, h1, h2, h3, h4,
    threeCoins_not_isConsistent_const hX hm hlaw⟩

end IVConsistencyExample

end CausalInference
