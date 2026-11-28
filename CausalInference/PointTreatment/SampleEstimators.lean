/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.PointTreatment.AugmentedWeighting
public import CausalInference.Estimation.LawOfLargeNumbers

/-!
# Point treatment: estimators as functions of an i.i.d. sample

The population model is a measure `μ` on `Ω` with covariates `W`, treatment `A` and potential
outcomes `Y`; its observed data are `D ω = (W ω, A ω, Y(A ω) ω)`. A sample is a sequence
`O : ℕ → Ξ → 𝒲 × Bool × ℝ` on a second probability space `(Ξ, P)` with
`CausalInference.IsIIDSample O P` and `P.map (O 0) = μ.map D`: the observations are independent
copies of the observed data. The estimators below are sample means of functions of an
observation `z = (w, b, y)`, built with `CausalInference.sampleMean`.

**Fitted nuisance functions.** A fitted score is a family `ê : ℕ → Ξ → 𝒲 → ℝ`: after `n`
observations, at the sample point `ξ`, the score `ê n ξ` is used. It may be computed from the
same sample. The convergence it must satisfy is `TendstoOnSample P O ê e`: for every `δ > 0`,
with probability tending to one, `|ê n ξ (W_i) - e (W_i)| ≤ δ` at every covariate value
`W_i` observed among the first `n`. Convergence in probability is defined through the outer
measure, so no measurability of `ê` is needed for the consistency theorems; measurability of
the estimators as functions of the sample is proved separately where it holds. Two sufficient
conditions are given: uniform convergence in probability on a set carrying the covariate law
(`TendstoOnSample.of_tendstoUniformlyOn`), and a parametric family `h θ` evaluated at a
consistent estimate `θ̂` of `θ₀`, for a family continuous in `θ` at `θ₀` uniformly in the
covariate (`TendstoOnSample.of_param`).

## Main definitions

* `armIndObs a z`: the indicator `1{b = a}` of an observation `z = (w, b, y)`.
* `ipwObs e a`, `ipwWeightObs e a`, `regObs m a`, `aipwObs e m a`: the weighted outcome, the
  weight, the regression and the augmented weighted outcome of an observation.
* `sampleIpwArmMean`, `sampleHajekArmMean`, `sampleIpwAte`, `sampleHajekAte`: the Horvitz and
  Thompson and the Hájek estimators; `sampleOrArmMean`, `sampleOrAte`: g-computation;
  `sampleAipwArmMean`, `sampleAipwAte`: the augmented estimators; `sampleArmMean`,
  `sampleNaiveContrast`: the observed arm means and their difference.
* `TendstoOnSample P O ĥ h`: the in-sample uniform convergence of a fitted function.

## Main results

* `ipwObs_comp`, `ipwWeightObs_comp`, `aipwObs_comp`: evaluated at the observed data, the
  observation functions are the population integrands `ipwTerm`, `ipwWeight`, `aipwTerm`.
* `isConsistent_sampleMean_of_map_eq`: the law of large numbers for a sample of the observed
  data, with the limit written as a population integral.
* `isConsistent_sampleMean_fitted`: a sample mean of fitted functions that are within
  `η g(O_i)` of a fixed function at the sampled points, for every `η > 0` with probability
  tending to one, has the limit of the sample mean of the fixed function.

## References

* A. W. van der Vaart, *Asymptotic Statistics*, Cambridge University Press (1998).
-/

@[expose] public section

namespace CausalInference

namespace PointTreatment

open MeasureTheory ProbabilityTheory MissingData Filter Finset
open scoped Topology

variable {Ω Ξ 𝒲 : Type*} {mΩ : MeasurableSpace Ω} {mΞ : MeasurableSpace Ξ} [MeasurableSpace 𝒲]

/-! ### Functions of an observation -/

section Observation

omit [MeasurableSpace 𝒲]

/-- The arm indicator `1{b = a}` of an observation `z = (w, b, y)`. -/
def armIndObs (a : Bool) (z : 𝒲 × Bool × ℝ) : ℝ := if z.2.1 = a then 1 else 0

/-- The weighted outcome `1{b = a} y / π_a(w)` of an observation, for a score `e`. -/
noncomputable def ipwObs (e : 𝒲 → ℝ) (a : Bool) (z : 𝒲 × Bool × ℝ) : ℝ :=
  armIndObs a z * z.2.2 / armProb e a z.1

/-- The weight `1{b = a} / π_a(w)` of an observation, for a score `e`. -/
noncomputable def ipwWeightObs (e : 𝒲 → ℝ) (a : Bool) (z : 𝒲 × Bool × ℝ) : ℝ :=
  armIndObs a z / armProb e a z.1

/-- The regression `m(a, w)` at the covariate of an observation. -/
def regObs (m : Bool → 𝒲 → ℝ) (a : Bool) (z : 𝒲 × Bool × ℝ) : ℝ := m a z.1

/-- The augmented weighted outcome of an observation,
`1{b = a} y / π_a(w) - (1{b = a} - π_a(w)) / π_a(w) · m(a, w)`. -/
noncomputable def aipwObs (e : 𝒲 → ℝ) (m : Bool → 𝒲 → ℝ) (a : Bool) (z : 𝒲 × Bool × ℝ) : ℝ :=
  ipwObs e a z - (armIndObs a z - armProb e a z.1) / armProb e a z.1 * m a z.1

theorem armIndObs_nonneg (a : Bool) (z : 𝒲 × Bool × ℝ) : 0 ≤ armIndObs a z := by
  unfold armIndObs; split_ifs <;> norm_num

theorem armIndObs_le_one (a : Bool) (z : 𝒲 × Bool × ℝ) : armIndObs a z ≤ 1 := by
  unfold armIndObs; split_ifs <;> norm_num

theorem abs_armIndObs_mul_le (a : Bool) (z : 𝒲 × Bool × ℝ) (x : ℝ) :
    |armIndObs a z * x| ≤ |x| := by
  unfold armIndObs; split_ifs <;> simp

/-- At the observed data `(W, A, Y)` the arm indicator is the response indicator of the arm. -/
theorem armIndObs_comp (W : Ω → 𝒲) (A : Ω → Bool) (Y : Bool → Ω → ℝ) (a : Bool) (ω : Ω) :
    armIndObs a (W ω, A ω, obsOutcome A Y ω) = respInd (arm A a) ω := by
  rw [respInd_arm_apply]; rfl

theorem ipwObs_comp (W : Ω → 𝒲) (A : Ω → Bool) (Y : Bool → Ω → ℝ) (e : 𝒲 → ℝ) (a : Bool) :
    (fun ω => ipwObs e a (W ω, A ω, obsOutcome A Y ω)) = ipwTerm A Y W e a := by
  funext ω; simp only [ipwObs, armIndObs_comp, ipwTerm]

theorem ipwWeightObs_comp (W : Ω → 𝒲) (A : Ω → Bool) (Y : Bool → Ω → ℝ) (e : 𝒲 → ℝ)
    (a : Bool) :
    (fun ω => ipwWeightObs e a (W ω, A ω, obsOutcome A Y ω)) = ipwWeight A W e a := by
  funext ω; simp only [ipwWeightObs, armIndObs_comp, ipwWeight]

theorem aipwObs_comp (W : Ω → 𝒲) (A : Ω → Bool) (Y : Bool → Ω → ℝ) (e : 𝒲 → ℝ)
    (m : Bool → 𝒲 → ℝ) (a : Bool) :
    (fun ω => aipwObs e m a (W ω, A ω, obsOutcome A Y ω)) = aipwTerm A Y W e m a := by
  funext ω; simp only [aipwObs, ipwObs, armIndObs_comp, aipwTerm]

end Observation

theorem measurable_armIndObs (a : Bool) : Measurable (armIndObs (𝒲 := 𝒲) a) :=
  (Measurable.of_discrete (f := fun b : Bool => if b = a then (1 : ℝ) else 0)).comp
    measurable_snd.fst

theorem measurable_ipwObs {e : 𝒲 → ℝ} (he : Measurable e) (a : Bool) :
    Measurable (ipwObs e a) :=
  ((measurable_armIndObs a).mul measurable_snd.snd).div ((measurable_armProb he a).comp
    measurable_fst)

theorem measurable_ipwWeightObs {e : 𝒲 → ℝ} (he : Measurable e) (a : Bool) :
    Measurable (ipwWeightObs e a) :=
  (measurable_armIndObs a).div ((measurable_armProb he a).comp measurable_fst)

theorem measurable_regObs {m : Bool → 𝒲 → ℝ} {a : Bool} (hm : Measurable (m a)) :
    Measurable (regObs m a) :=
  hm.comp measurable_fst

theorem measurable_aipwObs {e : 𝒲 → ℝ} {m : Bool → 𝒲 → ℝ} (he : Measurable e) {a : Bool}
    (hm : Measurable (m a)) : Measurable (aipwObs e m a) :=
  (measurable_ipwObs he a).sub ((((measurable_armIndObs a).sub ((measurable_armProb he a).comp
    measurable_fst)).div ((measurable_armProb he a).comp measurable_fst)).mul
      (hm.comp measurable_fst))

/-! ### The estimators -/

section Estimators

omit [MeasurableSpace 𝒲]

/-- The Horvitz and Thompson estimator of the arm mean `E[Y(a)]` with a (possibly fitted) score
`ê`: `n⁻¹ ∑_{i < n} 1{A_i = a} Y_i / π̂_a(W_i)`, with `π̂_a = armProb (ê n ξ) a`. For a known
score take `ê = fun _ _ => e`. -/
noncomputable def sampleIpwArmMean (ê : ℕ → Ξ → 𝒲 → ℝ) (a : Bool) (O : ℕ → Ξ → 𝒲 × Bool × ℝ)
    (n : ℕ) (ξ : Ξ) : ℝ :=
  sampleMean (ipwObs (ê n ξ) a) O n ξ

/-- The mean weight `n⁻¹ ∑_{i < n} 1{A_i = a} / π̂_a(W_i)` of the arm `a`. -/
noncomputable def sampleIpwWeightMean (ê : ℕ → Ξ → 𝒲 → ℝ) (a : Bool)
    (O : ℕ → Ξ → 𝒲 × Bool × ℝ) (n : ℕ) (ξ : Ξ) : ℝ :=
  sampleMean (ipwWeightObs (ê n ξ) a) O n ξ

/-- The Hájek estimator of the arm mean: the Horvitz and Thompson estimator divided by the mean
weight. Where the mean weight vanishes, the value is `0` by the convention `x / 0 = 0`; the
consistency theorems show that this happens with probability tending to zero. -/
noncomputable def sampleHajekArmMean (ê : ℕ → Ξ → 𝒲 → ℝ) (a : Bool)
    (O : ℕ → Ξ → 𝒲 × Bool × ℝ) (n : ℕ) (ξ : Ξ) : ℝ :=
  sampleIpwArmMean ê a O n ξ / sampleIpwWeightMean ê a O n ξ

/-- The Horvitz and Thompson estimator of the average effect. -/
noncomputable def sampleIpwAte (ê : ℕ → Ξ → 𝒲 → ℝ) (O : ℕ → Ξ → 𝒲 × Bool × ℝ) (n : ℕ)
    (ξ : Ξ) : ℝ :=
  sampleIpwArmMean ê true O n ξ - sampleIpwArmMean ê false O n ξ

/-- The Hájek estimator of the average effect. -/
noncomputable def sampleHajekAte (ê : ℕ → Ξ → 𝒲 → ℝ) (O : ℕ → Ξ → 𝒲 × Bool × ℝ) (n : ℕ)
    (ξ : Ξ) : ℝ :=
  sampleHajekArmMean ê true O n ξ - sampleHajekArmMean ê false O n ξ

/-- The g-computation (outcome regression plug-in) estimator of the arm mean with a (possibly
fitted) regression `m̂`: `n⁻¹ ∑_{i < n} m̂(a, W_i)`. -/
noncomputable def sampleOrArmMean (mh : ℕ → Ξ → Bool → 𝒲 → ℝ) (a : Bool)
    (O : ℕ → Ξ → 𝒲 × Bool × ℝ) (n : ℕ) (ξ : Ξ) : ℝ :=
  sampleMean (regObs (mh n ξ) a) O n ξ

/-- The g-computation estimator of the average effect. -/
noncomputable def sampleOrAte (mh : ℕ → Ξ → Bool → 𝒲 → ℝ) (O : ℕ → Ξ → 𝒲 × Bool × ℝ) (n : ℕ)
    (ξ : Ξ) : ℝ :=
  sampleOrArmMean mh true O n ξ - sampleOrArmMean mh false O n ξ

/-- The augmented inverse probability weighted estimator of the arm mean with a fitted score
`ê` and a fitted regression `m̂`. -/
noncomputable def sampleAipwArmMean (ê : ℕ → Ξ → 𝒲 → ℝ) (mh : ℕ → Ξ → Bool → 𝒲 → ℝ) (a : Bool)
    (O : ℕ → Ξ → 𝒲 × Bool × ℝ) (n : ℕ) (ξ : Ξ) : ℝ :=
  sampleMean (aipwObs (ê n ξ) (mh n ξ) a) O n ξ

/-- The augmented inverse probability weighted estimator of the average effect. -/
noncomputable def sampleAipwAte (ê : ℕ → Ξ → 𝒲 → ℝ) (mh : ℕ → Ξ → Bool → 𝒲 → ℝ)
    (O : ℕ → Ξ → 𝒲 × Bool × ℝ) (n : ℕ) (ξ : Ξ) : ℝ :=
  sampleAipwArmMean ê mh true O n ξ - sampleAipwArmMean ê mh false O n ξ

/-- The observed mean of the outcome in the arm `a`,
`∑_{i < n} 1{A_i = a} Y_i / ∑_{i < n} 1{A_i = a}`, written as a ratio of sample means; it is
`0` when no observation is in the arm. -/
noncomputable def sampleArmMean (a : Bool) (O : ℕ → Ξ → 𝒲 × Bool × ℝ) (n : ℕ) (ξ : Ξ) : ℝ :=
  sampleMean (fun z => armIndObs a z * z.2.2) O n ξ / sampleMean (armIndObs a) O n ξ

/-- The difference in observed arm means, the sample version of `naiveContrast`. -/
noncomputable def sampleNaiveContrast (O : ℕ → Ξ → 𝒲 × Bool × ℝ) (n : ℕ) (ξ : Ξ) : ℝ :=
  sampleArmMean true O n ξ - sampleArmMean false O n ξ

end Estimators

/-! ### Measurability as functions of the sample -/

/-- With a known measurable score, the Horvitz and Thompson estimator is a measurable function of
the sample. -/
theorem isSampleMeasurable_sampleIpwArmMean {e : 𝒲 → ℝ} (he : Measurable e) (a : Bool)
    (O : ℕ → Ξ → 𝒲 × Bool × ℝ) :
    IsSampleMeasurable (sampleIpwArmMean (fun _ _ => e) a O) O :=
  isSampleMeasurable_sampleMean (measurable_ipwObs he a) O

/-- With a known measurable regression, the g-computation estimator is a measurable function of
the sample. -/
theorem isSampleMeasurable_sampleOrArmMean {m : Bool → 𝒲 → ℝ} {a : Bool} (hm : Measurable (m a))
    (O : ℕ → Ξ → 𝒲 × Bool × ℝ) :
    IsSampleMeasurable (sampleOrArmMean (fun _ _ => m) a O) O :=
  isSampleMeasurable_sampleMean (measurable_regObs hm) O

/-- With a known measurable score and regression, the augmented estimator is a measurable
function of the sample. -/
theorem isSampleMeasurable_sampleAipwArmMean {e : 𝒲 → ℝ} {m : Bool → 𝒲 → ℝ} (he : Measurable e)
    {a : Bool} (hm : Measurable (m a)) (O : ℕ → Ξ → 𝒲 × Bool × ℝ) :
    IsSampleMeasurable (sampleAipwArmMean (fun _ _ => e) (fun _ _ => m) a O) O :=
  isSampleMeasurable_sampleMean (measurable_aipwObs he hm) O

/-- The observed arm mean is a measurable function of the sample. -/
theorem isSampleMeasurable_sampleArmMean (a : Bool) (O : ℕ → Ξ → 𝒲 × Bool × ℝ) :
    IsSampleMeasurable (sampleArmMean a O) O := by
  intro n
  obtain ⟨g₁, hg₁, h₁⟩ := isSampleMeasurable_sampleMean
    (f := fun z : 𝒲 × Bool × ℝ => armIndObs a z * z.2.2)
    ((measurable_armIndObs (𝒲 := 𝒲) a).mul measurable_snd.snd) O n
  obtain ⟨g₂, hg₂, h₂⟩ := isSampleMeasurable_sampleMean (measurable_armIndObs (𝒲 := 𝒲) a) O n
  refine ⟨fun x => g₁ x / g₂ x, hg₁.div hg₂, ?_⟩
  funext ξ
  simp only [sampleArmMean, congrFun h₁ ξ, congrFun h₂ ξ]

/-- The difference in observed arm means is a measurable function of the sample. -/
theorem isSampleMeasurable_sampleNaiveContrast (O : ℕ → Ξ → 𝒲 × Bool × ℝ) :
    IsSampleMeasurable (sampleNaiveContrast O) O := by
  intro n
  obtain ⟨g₁, hg₁, h₁⟩ := isSampleMeasurable_sampleArmMean true O n
  obtain ⟨g₂, hg₂, h₂⟩ := isSampleMeasurable_sampleArmMean false O n
  refine ⟨fun x => g₁ x - g₂ x, hg₁.sub hg₂, ?_⟩
  funext ξ
  simp only [sampleNaiveContrast, congrFun h₁ ξ, congrFun h₂ ξ]

/-! ### The law of large numbers for a sample of the observed data -/

variable {P : Measure Ξ} {O : ℕ → Ξ → 𝒲 × Bool × ℝ} {μ : Measure Ω}

/-- Integrability passes from the population to an observation with the same law. -/
theorem integrable_comp_of_map_eq {𝒪 : Type*} [MeasurableSpace 𝒪] {O : ℕ → Ξ → 𝒪}
    (hO : IsIIDSample O P) {D : Ω → 𝒪} (hD : AEMeasurable D μ) (hlaw : P.map (O 0) = μ.map D)
    {f : 𝒪 → ℝ} (hf : Measurable f) (hint : Integrable (fun ω => f (D ω)) μ) :
    Integrable (fun ξ => f (O 0 ξ)) P := by
  have hν : Integrable f (P.map (O 0)) := by
    rw [hlaw]; exact (integrable_map_measure hf.aestronglyMeasurable hD).2 hint
  exact (integrable_map_measure hf.aestronglyMeasurable (hO.aemeasurable 0)).1 hν

/-- A property of almost every covariate value under the population law holds for almost every
observation. -/
theorem ae_fst_of_map_eq {W : Ω → 𝒲} {A : Ω → Bool} {Y : Bool → Ω → ℝ}
    (hW : Measurable W) (hA : Measurable A) (hY : ∀ a, Measurable (Y a))
    (hlaw : P.map (O 0) = μ.map fun ω => (W ω, A ω, obsOutcome A Y ω)) {p : 𝒲 → Prop}
    (hp : ∀ᵐ w ∂(μ.map W), p w) : ∀ᵐ z ∂(P.map (O 0)), p z.1 := by
  have hD : Measurable fun ω => (W ω, A ω, obsOutcome A Y ω) :=
    hW.prodMk (hA.prodMk (measurable_obsOutcome hA hY))
  have hmap : (P.map (O 0)).map Prod.fst = μ.map W := by
    rw [hlaw, Measure.map_map measurable_fst hD]; rfl
  exact ae_of_ae_map measurable_fst.aemeasurable (hmap ▸ hp)

/-- **Law of large numbers for a sample of a population variable.** If the observations are an
i.i.d. sample with the law of `D` under `μ` and `f (D)` is integrable, the sample mean of `f` is
consistent for `∫ f (D ω) ∂μ`. -/
theorem isConsistent_sampleMean_of_map_eq [IsProbabilityMeasure P] {𝒪 : Type*}
    [MeasurableSpace 𝒪] {O : ℕ → Ξ → 𝒪} (hO : IsIIDSample O P) {D : Ω → 𝒪}
    (hD : AEMeasurable D μ) (hlaw : P.map (O 0) = μ.map D) {f : 𝒪 → ℝ} (hf : Measurable f)
    (hint : Integrable (fun ω => f (D ω)) μ) :
    IsConsistent (sampleMean f O) (∫ ω, f (D ω) ∂μ) P := by
  have h := sampleMean_isConsistent hO hf (integrable_comp_of_map_eq hO hD hlaw hf hint)
  have heq : ∫ ξ, f (O 0 ξ) ∂P = ∫ ω, f (D ω) ∂μ := by
    rw [← integral_map (hO.aemeasurable 0) hf.aestronglyMeasurable, hlaw,
      integral_map hD hf.aestronglyMeasurable]
  rwa [heq] at h

/-- **Fitted functions close to a fixed one at the sampled points.** Let `f₀` be a fixed
function whose sample mean is consistent for `c`, and `f n ξ` fitted functions such that, for
every `η > 0`, with probability tending to one, `|f n ξ (O_i) - f₀ (O_i)| ≤ η g(O_i)` for all
`i < n`, where `g (O 0)` is integrable. Then the sample mean of the fitted functions is
consistent for `c`. -/
theorem isConsistent_sampleMean_fitted [IsProbabilityMeasure P] {𝒪 : Type*} [MeasurableSpace 𝒪]
    {O : ℕ → Ξ → 𝒪} (hO : IsIIDSample O P) {f₀ : 𝒪 → ℝ} {c : ℝ}
    (h₀ : IsConsistent (sampleMean f₀ O) c P) {f : ℕ → Ξ → 𝒪 → ℝ} {g : 𝒪 → ℝ}
    (hg : Measurable g) (hgi : Integrable (fun ξ => g (O 0 ξ)) P)
    (hclose : ∀ η, 0 < η → WithProbTendingToOne P
      (fun n => {ξ | ∀ i < n, |f n ξ (O i ξ) - f₀ (O i ξ)| ≤ η * g (O i ξ)})) :
    IsConsistent (fun n ξ => sampleMean (f n ξ) O n ξ) c P := by
  refine TendstoInMeasure.of_perturb h₀ (sampleMean_isConsistent hO hg hgi)
    (fun η hη => (hclose η hη).mono fun n ξ hξ => ?_)
  simp only [Set.mem_ofPred_eq] at hξ ⊢
  simp only [sampleMean]
  rw [← mul_sub, ← Finset.sum_sub_distrib, abs_mul,
    abs_of_nonneg (inv_nonneg.2 (Nat.cast_nonneg n))]
  calc (n : ℝ)⁻¹ * |∑ i ∈ range n, (f n ξ (O i ξ) - f₀ (O i ξ))|
      ≤ (n : ℝ)⁻¹ * ∑ i ∈ range n, η * g (O i ξ) :=
        mul_le_mul_of_nonneg_left ((Finset.abs_sum_le_sum_abs _ _).trans
          (Finset.sum_le_sum fun i hi => hξ i (Finset.mem_range.1 hi)))
          (inv_nonneg.2 (Nat.cast_nonneg n))
    _ = η * ((n : ℝ)⁻¹ * ∑ i ∈ range n, g (O i ξ)) := by
        rw [← Finset.mul_sum]; ring

/-! ### Fitted nuisance functions -/

/-- **In-sample uniform convergence of a fitted function.** The fitted functions
`ĥ n ξ : 𝒲 → ℝ` converge to `h` at the sampled covariates: for every `δ > 0`, with probability
tending to one, `|ĥ n ξ (W_i) - h (W_i)| ≤ δ` for all `i < n`. -/
def TendstoOnSample (P : Measure Ξ) (O : ℕ → Ξ → 𝒲 × Bool × ℝ) (ĥ : ℕ → Ξ → 𝒲 → ℝ)
    (h : 𝒲 → ℝ) : Prop :=
  ∀ δ, 0 < δ → WithProbTendingToOne P
    (fun n => {ξ | ∀ i < n, |ĥ n ξ (O i ξ).1 - h (O i ξ).1| ≤ δ})

omit [MeasurableSpace 𝒲] in
/-- A function that does not depend on the sample converges to itself. -/
theorem tendstoOnSample_const (P : Measure Ξ) (O : ℕ → Ξ → 𝒲 × Bool × ℝ) (h : 𝒲 → ℝ) :
    TendstoOnSample P O (fun _ _ => h) h := fun δ hδ =>
  (withProbTendingToOne_univ (μ := P)).mono fun n ξ _ i _ => by
    simp only [sub_self, abs_zero]; exact hδ.le

/-- **Uniform convergence on the support suffices.** If `ĥ n → h` uniformly on a set `K` in
probability and the covariate of an observation lies in `K` almost surely, then `ĥ` converges
to `h` on the sample. -/
theorem TendstoOnSample.of_tendstoUniformlyOn (hO : IsIIDSample O P) {ĥ : ℕ → Ξ → 𝒲 → ℝ}
    {h : 𝒲 → ℝ} {K : Set 𝒲} (hunif : TendstoUniformlyOnInProbability P ĥ h K)
    (hK : ∀ᵐ z ∂(P.map (O 0)), z.1 ∈ K) : TendstoOnSample P O ĥ h := fun δ hδ =>
  ((hunif δ hδ).inter (WithProbTendingToOne.of_ae (hO.ae_forall hK))).mono
    fun n ξ hξ i _ => by
      obtain ⟨h1, h2⟩ := hξ
      simp only [Set.mem_ofPred_eq] at h1 h2
      exact (h1 _ (h2 i)).le

omit [MeasurableSpace 𝒲] in
/-- **A parametric family at a consistent parameter estimate.** Let `h : Θ → 𝒲 → ℝ` be a family
that is continuous in the parameter at `θ₀` uniformly in the covariate, and let `θ̂` converge
in probability to `θ₀`. Then the fitted functions `h (θ̂ n ξ)` converge to `h θ₀` on the
sample (in fact uniformly in the covariate). -/
theorem TendstoOnSample.of_param {Θ : Type*} [PseudoMetricSpace Θ] {h : Θ → 𝒲 → ℝ} {θ₀ : Θ}
    (hcont : ∀ ε, 0 < ε → ∃ δ, 0 < δ ∧ ∀ θ, dist θ θ₀ < δ → ∀ w, |h θ w - h θ₀ w| ≤ ε)
    {θh : ℕ → Ξ → Θ} (hθ : TendstoInMeasure P θh atTop (fun _ => θ₀)) :
    TendstoOnSample P O (fun n ξ => h (θh n ξ)) (h θ₀) := fun ε hε => by
  obtain ⟨δ, hδ, hδh⟩ := hcont ε hε
  exact (hθ.withProbTendingToOne_dist_lt hδ).mono fun n ξ hξ i _ => hδh _ hξ _

end PointTreatment

end CausalInference
