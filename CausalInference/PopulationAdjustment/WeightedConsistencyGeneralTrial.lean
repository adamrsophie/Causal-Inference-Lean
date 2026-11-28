/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.PopulationAdjustment.WeightedConsistencyGeneralArm
public import CausalInference.PopulationAdjustment.UnanchoredIdentification
public import CausalInference.PopulationAdjustment.AnchoredIdentification

/-!
# The weighted estimator for the individual data of a randomized trial

The consistency theorems of `WeightedConsistencyGeneralArm` are stated for the law of a record
`(X, A, Y)`: a regression of the reweighted arm, a square integrable residual on the arm and a
bounded conditional variance, all with respect to `σ(X, A)`. This file derives those hypotheses
from the primitives of a randomized trial `T` (`Trial`): the assignment `A` independent of the
pair `(X, Y(a))`, the conditional mean `E[Y(a) | X] = m(X)` (`Population.IsCondMean`), a square
integrable residual `Y(a) - m(X)`, and a bounded conditional variance
`E[(Y(a) - m(X))² | X] ≤ σ²`.

**Which regression is needed.** `sampleBalancedArmMean_isConsistent_trial` assumes a
measurable regression surface `μ_s` for both arms and a regression `E[Y | X, A] = μ_A(X)` of
the observed outcome. Only arm `a` enters the weighted mean of arm `a`: its residual noise is
`1{A = a}(Y - μ_a(X))`, so the regression of the other arm is not needed, and the measurability
of `μ_a` follows from `μ_a = a₀ + bᵀφ` and the measurability of `φ`. The hypotheses below
concern `Y(a)` only.

**The transfer.** For a set `S` of `σ(X, A)` in the record space and a function `k(x, y)`,
`E[1{A = a} k(X, Y) ; (X, A) ∈ S] = P(A = a) E[k(X, Y(a)) ; X ∈ S_a]` with
`S_a = {x | (x, a) ∈ S}` (`setIntegral_ipdLaw_armInd`), since `Y = Y(a)` on `{A = a}` and `A` is
independent of `(X, Y(a))`. A conditional mean `r(X)` of `k(X, Y(a))` given `X` therefore gives
the conditional mean `1{A = a} r(X)` of `1{A = a} k(X, Y)` given `(X, A)`
(`condExp_ipdLaw_armInd`), which yields the regression and the variance bound of the record law.

## Main results

* `setIntegral_ipdLaw_armInd`, `condExp_ipdLaw_armInd`.
* `ipdLaw_arm_hypotheses`: the record law hypotheses from the trial primitives.
* `sampleBalancedArmMean_isConsistent_trial_general`: consistency for the individual data of a
  randomized trial, with random targets, unbounded features and the interior condition.
* `sampleBalancedArmMean_isConsistent_trial_armMean`: the limit is the target arm mean.
* `unanchoredBalancedEstimate_isConsistent_trial`: composed with the unanchored identification
  theorem, the unanchored comparison is consistent for the target effect.
* `anchoredBalancedEstimate_isConsistent_trial`: the anchored comparison on a link scale.
* `anchoredBalancedEstimate_isConsistent_identity_trial`: composed with the anchored
  identification theorem on the identity scale, the anchored comparison is consistent for the
  anchored estimand, which is the target effect.

## References

* J. E. Signorovitch and coauthors, PharmacoEconomics 28 (2010).
* D. M. Phillippo, A. E. Ades, S. Dias, S. Palmer, K. R. Abrams and N. J. Welton, *Methods for
  population-adjusted indirect comparisons in health technology appraisal*, Medical Decision
  Making 38 (2018).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Finset
open scoped Topology ENNReal

namespace CausalInference

namespace PopulationAdjustment

open PointTreatment IndirectComparison EffectMeasure

variable {Ω₁ 𝒳 : Type*} [MeasurableSpace Ω₁] [MeasurableSpace 𝒳] {T : Trial Ω₁ 𝒳 Bool}

omit [MeasurableSpace 𝒳] in
/-- On the arm `a`, the observed outcome is the potential outcome of `a`. -/
theorem armIndObs_mul_obsOutcome (a : Bool) (k : 𝒳 × ℝ → ℝ) (ω : Ω₁) :
    armIndObs a (T.X ω, T.A ω, T.obsOutcome ω) * k (T.X ω, T.obsOutcome ω) =
      armIndObs a (T.X ω, T.A ω, T.obsOutcome ω) * k (T.X ω, T.Y a ω) := by
  unfold armIndObs
  split_ifs with h
  · simp only at h; simp [Trial.obsOutcome, h]
  · simp

/-- **Transfer of arm integrals to the trial.** For a measurable set `S` of covariate and arm
values and a measurable `k(x, y)` with `k(X, Y(a))` integrable, if `A` is independent of
`(X, Y(a))`, then `E[1{A = a} k(X, Y) ; (X, A) ∈ S] = P(A = a) E[k(X, Y(a)) ; X ∈ S_a]`. -/
theorem setIntegral_ipdLaw_armInd [IsProbabilityMeasure T.μ] (hX : Measurable T.X)
    (hA : Measurable T.A) (hYo : Measurable T.obsOutcome) (a : Bool)
    (hYa : Measurable (T.Y a)) (hind : IndepFun T.A (fun ω => (T.X ω, T.Y a ω)) T.μ)
    {k : 𝒳 × ℝ → ℝ} (hk : Measurable k) {S : Set (𝒳 × Bool)} (hS : MeasurableSet S) :
    ∫ z in (fun z : 𝒳 × Bool × ℝ => (z.1, z.2.1)) ⁻¹' S, armIndObs a z * k (z.1, z.2.2)
        ∂T.ipdLaw =
      T.μ.real (T.A ⁻¹' {a}) * ∫ ω in T.X ⁻¹' ((fun x => (x, a)) ⁻¹' S), k (T.X ω, T.Y a ω)
        ∂T.μ := by
  have hf : Measurable fun ω => (T.X ω, T.A ω, T.obsOutcome ω) := hX.prodMk (hA.prodMk hYo)
  have hπ : Measurable fun z : 𝒳 × Bool × ℝ => (z.1, z.2.1) :=
    measurable_fst.prodMk measurable_snd.fst
  have hSa : MeasurableSet ((fun x => (x, a)) ⁻¹' S) :=
    (measurable_id.prodMk measurable_const) hS
  have hg : Measurable fun z : 𝒳 × Bool × ℝ => armIndObs a z * k (z.1, z.2.2) :=
    (measurable_armIndObs a).mul (hk.comp (measurable_fst.prodMk measurable_snd.snd))
  rw [Trial.ipdLaw, setIntegral_map (hπ hS) hg.aestronglyMeasurable hf.aemeasurable,
    ← integral_indicator (hf (hπ hS)), ← integral_indicator (hX hSa)]
  have hpt : ((fun ω => (T.X ω, T.A ω, T.obsOutcome ω)) ⁻¹'
      ((fun z : 𝒳 × Bool × ℝ => (z.1, z.2.1)) ⁻¹' S)).indicator
        (fun ω => armIndObs a (T.X ω, T.A ω, T.obsOutcome ω) * k (T.X ω, T.obsOutcome ω)) =
      fun ω => (fun s : Bool => if s = a then (1 : ℝ) else 0) (T.A ω) *
        (fun q : 𝒳 × ℝ => ((fun x => (x, a)) ⁻¹' S).indicator (fun x => k (x, q.2)) q.1)
          (T.X ω, T.Y a ω) := by
    funext ω
    by_cases h : T.A ω = a
    · have hobs : T.obsOutcome ω = T.Y a ω := by simp [Trial.obsOutcome, h]
      by_cases hm : (T.X ω, a) ∈ S <;> simp [Set.indicator, armIndObs, h, hobs, hm]
    · simp only [Set.indicator, Set.mem_preimage, armIndObs, h, ite_false, zero_mul]
      split_ifs <;> rfl
  have hgm : Measurable fun q : 𝒳 × ℝ =>
      ((fun x => (x, a)) ⁻¹' S).indicator (fun x => k (x, q.2)) q.1 := by
    have : (fun q : 𝒳 × ℝ => ((fun x => (x, a)) ⁻¹' S).indicator (fun x => k (x, q.2)) q.1) =
        (Prod.fst ⁻¹' ((fun x => (x, a)) ⁻¹' S)).indicator k := by
      funext q; by_cases hm : (q.1, a) ∈ S <;> simp [Set.indicator, hm]
    rw [this]; exact hk.indicator (measurable_fst hSa)
  have hprod := hind.integral_fun_comp_mul_comp (f := fun s : Bool => if s = a then (1 : ℝ) else 0)
    (g := fun q : 𝒳 × ℝ => ((fun x => (x, a)) ⁻¹' S).indicator (fun x => k (x, q.2)) q.1)
    hA.aemeasurable (hX.prodMk hYa).aemeasurable
    (measurable_of_countable _).aestronglyMeasurable hgm.aestronglyMeasurable
  rw [hpt, hprod]
  congr 1
  · rw [show (fun ω => (fun s : Bool => if s = a then (1 : ℝ) else 0) (T.A ω)) =
        (T.A ⁻¹' {a}).indicator 1 from funext fun ω => by
          simp [Set.indicator, Set.mem_preimage]]
    exact integral_indicator_one (hA (measurableSet_singleton a))

theorem isProbabilityMeasure_ipdLaw_of_trial [IsProbabilityMeasure T.μ] :
    IsProbabilityMeasure T.ipdLaw := by
  unfold Trial.ipdLaw; infer_instance

/-- **Transfer of conditional means to the record law.** If `A` is independent of `(X, Y(a))` and
`r(X)` is a version of `E[k(X, Y(a)) | X]` for an integrable `k(X, Y(a))`, then
`1{A = a} r(X)` is a version of `E[1{A = a} k(X, Y) | X, A]` under the law of the records. -/
theorem condExp_ipdLaw_armInd [IsProbabilityMeasure T.μ] (hX : Measurable T.X)
    (hA : Measurable T.A) (hYo : Measurable T.obsOutcome) (a : Bool)
    (hYa : Measurable (T.Y a)) (hind : IndepFun T.A (fun ω => (T.X ω, T.Y a ω)) T.μ)
    {k : 𝒳 × ℝ → ℝ} (hk : Measurable k) (hki : Integrable (fun ω => k (T.X ω, T.Y a ω)) T.μ)
    {r : 𝒳 → ℝ} (hr : Measurable r)
    (hrk : (fun ω => r (T.X ω)) =ᵐ[T.μ]
      T.μ[fun ω => k (T.X ω, T.Y a ω) | MeasurableSpace.comap T.X inferInstance]) :
    T.ipdLaw[fun z => armIndObs a z * k (z.1, z.2.2) | MeasurableSpace.comap
      (fun z : 𝒳 × Bool × ℝ => (z.1, z.2.1)) inferInstance] =ᵐ[T.ipdLaw]
        fun z => armIndObs a z * r z.1 := by
  have := isProbabilityMeasure_ipdLaw_of_trial (T := T)
  have hf : Measurable fun ω => (T.X ω, T.A ω, T.obsOutcome ω) := hX.prodMk (hA.prodMk hYo)
  have hπ : Measurable fun z : 𝒳 × Bool × ℝ => (z.1, z.2.1) :=
    measurable_fst.prodMk measurable_snd.fst
  have hm : MeasurableSpace.comap (fun z : 𝒳 × Bool × ℝ => (z.1, z.2.1))
      (inferInstance : MeasurableSpace (𝒳 × Bool)) ≤
        (inferInstance : MeasurableSpace (𝒳 × Bool × ℝ)) := hπ.comap_le
  have hmX : MeasurableSpace.comap T.X (inferInstance : MeasurableSpace 𝒳) ≤
      (inferInstance : MeasurableSpace Ω₁) := hX.comap_le
  have hri : Integrable (fun ω => r (T.X ω)) T.μ := integrable_condExp.congr hrk.symm
  have hle : ∀ z : 𝒳 × Bool × ℝ, ∀ u : ℝ, ‖armIndObs a z * u‖ ≤ ‖u‖ := fun z u => by
    rcases armIndObs_eq_zero_or_one a z with h | h <;> simp [h]
  have hgk : Measurable fun z : 𝒳 × Bool × ℝ => armIndObs a z * k (z.1, z.2.2) :=
    (measurable_armIndObs a).mul (hk.comp (measurable_fst.prodMk measurable_snd.snd))
  have hgr : Measurable fun z : 𝒳 × Bool × ℝ => armIndObs a z * r z.1 :=
    (measurable_armIndObs a).mul (hr.comp measurable_fst)
  have hint : ∀ {u : 𝒳 × ℝ → ℝ}, Measurable u →
      Integrable (fun ω => u (T.X ω, T.Y a ω)) T.μ →
      Integrable (fun z : 𝒳 × Bool × ℝ => armIndObs a z * u (z.1, z.2.2)) T.ipdLaw := by
    intro u hu hui
    have hgu : Measurable fun z : 𝒳 × Bool × ℝ => armIndObs a z * u (z.1, z.2.2) :=
      (measurable_armIndObs a).mul (hu.comp (measurable_fst.prodMk measurable_snd.snd))
    rw [Trial.ipdLaw, integrable_map_measure hgu.aestronglyMeasurable hf.aemeasurable]
    refine hui.mono (hgu.comp hf).aestronglyMeasurable (ae_of_all _ fun ω => ?_)
    simp only [Function.comp_apply]
    rw [armIndObs_mul_obsOutcome a u ω]
    exact hle _ _
  refine (ae_eq_condExp_of_forall_setIntegral_eq hm (hint hk hki)
    (fun s _ _ => (hint (u := fun q => r q.1) (hr.comp measurable_fst) hri).integrableOn)
    (fun s hs _ => ?_) ?_).symm
  · obtain ⟨S, hS, rfl⟩ := hs
    have e1 := setIntegral_ipdLaw_armInd hX hA hYo a hYa hind (k := fun q : 𝒳 × ℝ => r q.1)
      (hr.comp measurable_fst) hS
    have e2 := setIntegral_ipdLaw_armInd hX hA hYo a hYa hind hk hS
    simp only at e1
    rw [e1, e2]
    congr 1
    have hSa : MeasurableSet[MeasurableSpace.comap T.X inferInstance]
        (T.X ⁻¹' ((fun x => (x, a)) ⁻¹' S)) :=
      ⟨_, (measurable_id.prodMk measurable_const) hS, rfl⟩
    rw [setIntegral_congr_ae (hmX _ hSa) (hrk.mono fun ω h _ => h),
      setIntegral_condExp hmX hki hSa]
  · have hc : Measurable[MeasurableSpace.comap (fun z : 𝒳 × Bool × ℝ => (z.1, z.2.1))
        inferInstance] fun z : 𝒳 × Bool × ℝ => armIndObs a z * r z.1 := by
      have h2 : Measurable fun q : 𝒳 × Bool => (if q.2 = a then (1 : ℝ) else 0) * r q.1 :=
        ((measurable_of_countable (fun s : Bool => if s = a then (1 : ℝ) else 0)).comp
          measurable_snd).mul (hr.comp measurable_fst)
      exact h2.comp (comap_measurable _)
    exact hc.aestronglyMeasurable

/-- `1{A = a} u(X, Y)` is integrable under the law of the records when `u(X, Y(a))` is
integrable. -/
theorem integrable_ipdLaw_armInd (hX : Measurable T.X) (hA : Measurable T.A)
    (hYo : Measurable T.obsOutcome) (a : Bool) {u : 𝒳 × ℝ → ℝ} (hu : Measurable u)
    (hui : Integrable (fun ω => u (T.X ω, T.Y a ω)) T.μ) :
    Integrable (fun z : 𝒳 × Bool × ℝ => armIndObs a z * u (z.1, z.2.2)) T.ipdLaw := by
  have hf : Measurable fun ω => (T.X ω, T.A ω, T.obsOutcome ω) := hX.prodMk (hA.prodMk hYo)
  have hgu : Measurable fun z : 𝒳 × Bool × ℝ => armIndObs a z * u (z.1, z.2.2) :=
    (measurable_armIndObs a).mul (hu.comp (measurable_fst.prodMk measurable_snd.snd))
  rw [Trial.ipdLaw, integrable_map_measure hgu.aestronglyMeasurable hf.aemeasurable]
  refine hui.mono (hgu.comp hf).aestronglyMeasurable (ae_of_all _ fun ω => ?_)
  simp only [Function.comp_apply]
  rw [armIndObs_mul_obsOutcome a u ω]
  rcases armIndObs_eq_zero_or_one a (T.X ω, T.A ω, T.obsOutcome ω) with h | h <;> simp [h]

/-- **The record law hypotheses from the trial primitives.** Let `T` be a trial with measurable
covariates, assignment, observed outcome and potential outcome `Y(a)`, randomized in the sense
that `A` is independent of `(X, Y(a))`. Let `m` be a conditional mean function of `Y(a)` given
`X` with a square integrable residual `Y(a) - m(X)` of conditional variance at most `σ²`. Then
under the law of the records: `X` and `A` are independent, the residual on arm `a` is square
integrable, `E[1{A = a} Y | X, A] = 1{A = a} m(X)`, and
`E[1{A = a}(Y - m(X))² | X, A] ≤ max σ² 0`. -/
theorem ipdLaw_arm_hypotheses [IsProbabilityMeasure T.μ] (hX : Measurable T.X)
    (hA : Measurable T.A) (hYo : Measurable T.obsOutcome) (a : Bool)
    (hYa : Measurable (T.Y a)) (hrand : IndepFun T.A (fun ω => (T.X ω, T.Y a ω)) T.μ)
    {m : 𝒳 → ℝ} (hm : T.IsCondMean a m)
    (hres2 : Integrable (fun ω => (T.Y a ω - m (T.X ω)) ^ 2) T.μ) {σ2 : ℝ}
    (hvar : T.μ[fun ω => (T.Y a ω - m (T.X ω)) ^ 2 | MeasurableSpace.comap T.X inferInstance]
      ≤ᵐ[T.μ] fun _ => σ2) :
    IndepFun (fun z : 𝒳 × Bool × ℝ => z.1) (fun z => z.2.1) T.ipdLaw ∧
    Integrable (fun z : 𝒳 × Bool × ℝ => armIndObs a z * (z.2.2 - m z.1) ^ 2) T.ipdLaw ∧
    T.ipdLaw[fun z => armIndObs a z * z.2.2 | MeasurableSpace.comap
      (fun z : 𝒳 × Bool × ℝ => (z.1, z.2.1)) inferInstance] =ᵐ[T.ipdLaw]
        (fun z => armIndObs a z * m z.1) ∧
    T.ipdLaw[fun z => armIndObs a z * (z.2.2 - m z.1) ^ 2 | MeasurableSpace.comap
      (fun z : 𝒳 × Bool × ℝ => (z.1, z.2.1)) inferInstance] ≤ᵐ[T.ipdLaw]
        fun _ => max σ2 0 := by
  have hf : Measurable fun ω => (T.X ω, T.A ω, T.obsOutcome ω) := hX.prodMk (hA.prodMk hYo)
  have hmX : MeasurableSpace.comap T.X (inferInstance : MeasurableSpace 𝒳) ≤
      (inferInstance : MeasurableSpace Ω₁) := hX.comap_le
  have hk2 : Measurable fun q : 𝒳 × ℝ => (q.2 - m q.1) ^ 2 :=
    (measurable_snd.sub (hm.1.comp measurable_fst)).pow_const 2
  have hYi : Integrable (T.Y a) T.μ :=
    integrable_of_condExp_eq_of_sq (MeasurableSpace.comap T.X inferInstance) hYa
      (hm.1.comp hX) hm.2.symm hres2
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact (indepFun_map_iff hf measurable_fst measurable_snd.fst).2
      (hrand.comp measurable_id measurable_fst).symm
  · exact integrable_ipdLaw_armInd hX hA hYo a hk2 hres2
  · exact condExp_ipdLaw_armInd hX hA hYo a hYa hrand (k := fun q : 𝒳 × ℝ => q.2) measurable_snd
      hYi hm.1 hm.2
  · obtain ⟨V, hVm, hVeq⟩ := (stronglyMeasurable_condExp (m := MeasurableSpace.comap T.X
      inferInstance) (μ := T.μ) (f := fun ω => (T.Y a ω - m (T.X ω)) ^ 2)).exists_eq_measurable_comp
    have hV := condExp_ipdLaw_armInd hX hA hYo a hYa hrand hk2 hres2 hVm.measurable
      (by rw [hVeq]; rfl)
    refine hV.le.trans ?_
    have hVle : ∀ᵐ ω ∂T.μ, V (T.X ω) ≤ σ2 := by
      filter_upwards [hvar] with ω hω
      have : V (T.X ω) = T.μ[fun ω => (T.Y a ω - m (T.X ω)) ^ 2 |
          MeasurableSpace.comap T.X inferInstance] ω := by rw [hVeq]; rfl
      rw [this]; exact hω
    have hVle' : ∀ᵐ z ∂T.ipdLaw, V z.1 ≤ σ2 := by
      rw [Trial.ipdLaw, ae_map_iff hf.aemeasurable
        (measurableSet_le (f := fun z : 𝒳 × Bool × ℝ => V z.1)
          (hVm.measurable.comp measurable_fst) measurable_const)]
      exact hVle
    filter_upwards [hVle'] with z hz
    rcases armIndObs_eq_zero_or_one a z with h | h <;> simp only [h, zero_mul, one_mul]
    · exact le_max_right _ _
    · exact hz.trans (le_max_left _ _)

/-- The mean of an affine function of integrable features is the affine function of the feature
means. -/
theorem integral_affine_features_of_integrable {𝒟 : Type*} [MeasurableSpace 𝒟] {ν : Measure 𝒟}
    [IsProbabilityMeasure ν] {p : ℕ} {φ : 𝒟 → Fin p → ℝ}
    (hφi : ∀ k, Integrable (fun x => φ x k) ν) {t : Fin p → ℝ}
    (ht : ∀ k, ∫ x, φ x k ∂ν = t k) (a0 : ℝ) (b : Fin p → ℝ) :
    ∫ x, (a0 + b ⬝ᵥ φ x) ∂ν = a0 + b ⬝ᵥ t := by
  have hs : Integrable (fun x => ∑ k, b k * φ x k) ν :=
    integrable_finsetSum _ fun k _ => (hφi k).const_mul (b k)
  simp only [dotProduct]
  rw [integral_add (integrable_const a0) hs, integral_const, probReal_univ, one_smul,
    integral_finsetSum _ fun k _ => (hφi k).const_mul (b k)]
  simp only [integral_const_mul, ht]

section Consistency

variable {Ω 𝒲 : Type*} [MeasurableSpace Ω] [MeasurableSpace 𝒲] {p : ℕ}
  {P : Measure Ω} [IsProbabilityMeasure P] {O : ℕ → Ω → 𝒳 × Bool × ℝ}

/-- **Consistency of the weighted arm mean for the individual data of a randomized trial.** Let
`T` be a trial with measurable covariates, assignment, observed outcome and potential outcome
`Y(a)`, randomized in the sense that `A` is independent of `(X, Y(a))`, and let `O` be an i.i.d.
sample of its individual data. Assume:
* `t` lies in the interior of the closed convex hull of the support of the law of `φ(X)`, and
  `E[exp(κ ‖φ(X) - t‖)] < ∞` for every `κ`;
* reported targets `tₙ = Gₙ(W) → t` in probability, computed from data `W` independent of the
  sample (deterministic targets are the case of constant `W`);
* `P(A = a) > 0`, a conditional mean `E[Y(a) | X] = m(X)` with `m = a₀ + bᵀφ`, a square
  integrable residual `Y(a) - m(X)` and `E[(Y(a) - m(X))² | X] ≤ σ²`.
Then the weighted arm mean at `tₙ` is consistent for `a₀ + bᵀt`. Nothing is assumed about the
potential outcome of the other arm. -/
theorem sampleBalancedArmMean_isConsistent_trial_general (hX : Measurable T.X)
    (hA : Measurable T.A) (hYo : Measurable T.obsOutcome) (a : Bool)
    (hYa : Measurable (T.Y a)) (hrand : IndepFun T.A (fun ω => (T.X ω, T.Y a ω)) T.μ)
    (hO : IsIIDSample O P) (hOm : ∀ i, Measurable (O i)) (hlaw : P.map (O 0) = T.ipdLaw)
    {φ : 𝒳 → Fin p → ℝ} (hφ : Measurable φ) {t : Fin p → ℝ}
    (hint : t ∈ interior (closedConvexHull ℝ (T.covLaw.map φ).support))
    (hexp : ∀ κ : ℝ, Integrable (fun x => Real.exp (κ * ‖φ x - t‖)) T.covLaw)
    {W : Ω → 𝒲} (hW : Measurable W) (hWO : IndepFun W (fun ω k => O k ω) P)
    {G : ℕ → 𝒲 → Fin p → ℝ} (hG : ∀ n, Measurable (G n))
    (htm : TendstoInMeasure P (fun n ω => G n (W ω)) atTop (fun _ => t))
    (hq : 0 < T.μ.real (T.A ⁻¹' {a})) {m : 𝒳 → ℝ} (hm : T.IsCondMean a m)
    (hres2 : Integrable (fun ω => (T.Y a ω - m (T.X ω)) ^ 2) T.μ) {σ2 : ℝ}
    (hvar : T.μ[fun ω => (T.Y a ω - m (T.X ω)) ^ 2 | MeasurableSpace.comap T.X inferInstance]
      ≤ᵐ[T.μ] fun _ => σ2)
    {a0 : ℝ} {b : Fin p → ℝ} (haff : ∀ x, m x = a0 + b ⬝ᵥ φ x) :
    IsConsistent (fun n ω => sampleBalancedArmMean φ (G n (W ω)) O a n ω) (a0 + b ⬝ᵥ t) P := by
  have hf : Measurable fun ω => (T.X ω, T.A ω, T.obsOutcome ω) := hX.prodMk (hA.prodMk hYo)
  have : IsProbabilityMeasure (T.μ.map fun ω => (T.X ω, T.A ω, T.obsOutcome ω)) := by
    change IsProbabilityMeasure T.ipdLaw
    rw [← hlaw]; infer_instance
  have : IsProbabilityMeasure T.μ := Measure.isProbabilityMeasure_of_map hf.aemeasurable
  obtain ⟨hind, hres2', hreg', hvar'⟩ :=
    ipdLaw_arm_hypotheses hX hA hYo a hYa hrand hm hres2 hvar
  have hmapφ : (T.ipdLaw.map fun z : 𝒳 × Bool × ℝ => φ z.1) = T.covLaw.map φ := by
    rw [Trial.ipdLaw, Population.covLaw,
      Measure.map_map (g := fun z : 𝒳 × Bool × ℝ => φ z.1) (hφ.comp measurable_fst) hf,
      Measure.map_map hφ hX]
    rfl
  have hint' : t ∈ interior (closedConvexHull ℝ
      ((P.map (O 0)).map fun z : 𝒳 × Bool × ℝ => φ z.1).support) := by
    rw [hlaw, hmapφ]; exact hint
  have hexp' : ∀ κ : ℝ, Integrable (fun z : 𝒳 × Bool × ℝ => Real.exp (κ * ‖φ z.1 - t‖))
      (P.map (O 0)) := fun κ => by
    have hm1 : Measurable fun x : 𝒳 => Real.exp (κ * ‖φ x - t‖) :=
      Real.measurable_exp.comp (measurable_const.mul (hφ.sub_const t).norm)
    have h1 := hexp κ
    rw [Population.covLaw, integrable_map_measure hm1.aestronglyMeasurable hX.aemeasurable]
      at h1
    have hm2 : Measurable fun z : 𝒳 × Bool × ℝ => Real.exp (κ * ‖φ z.1 - t‖) :=
      hm1.comp measurable_fst
    rw [hlaw, Trial.ipdLaw, integrable_map_measure hm2.aestronglyMeasurable hf.aemeasurable]
    exact h1
  have hq' : 0 < T.ipdLaw.real {z | z.2.1 = a} := by
    rw [Trial.ipdLaw, map_measureReal_apply hf
      (measurableSet_eq_fun measurable_snd.fst measurable_const)]
    exact hq
  rw [← hlaw] at hind hres2' hreg' hvar' hq'
  exact sampleBalancedArmMean_isConsistent_of_interior_of_integrable_exp hO hOm hφ hint' hexp'
    hW hWO hG htm hind a hq' hres2' hreg' hvar' haff

/-- **The limit is the target mean of the arm.** In addition to the assumptions of
`sampleBalancedArmMean_isConsistent_trial_general`, let `Q` be a target population whose feature
means are `t` (with integrable features under its covariate law) and in which `m` is a
conditional mean function of the integrable outcome `Y(a)`. Then the weighted arm mean at the
targets `tₙ` is consistent for the target arm mean `E_Q[Y(a)]`. -/
theorem sampleBalancedArmMean_isConsistent_trial_armMean {Ω' ι : Type*} [MeasurableSpace Ω']
    (hX : Measurable T.X)
    (hA : Measurable T.A) (hYo : Measurable T.obsOutcome) (a : Bool)
    (hYa : Measurable (T.Y a)) (hrand : IndepFun T.A (fun ω => (T.X ω, T.Y a ω)) T.μ)
    (hO : IsIIDSample O P) (hOm : ∀ i, Measurable (O i)) (hlaw : P.map (O 0) = T.ipdLaw)
    {φ : 𝒳 → Fin p → ℝ} (hφ : Measurable φ) {t : Fin p → ℝ}
    (hint : t ∈ interior (closedConvexHull ℝ (T.covLaw.map φ).support))
    (hexp : ∀ κ : ℝ, Integrable (fun x => Real.exp (κ * ‖φ x - t‖)) T.covLaw)
    {W : Ω → 𝒲} (hW : Measurable W) (hWO : IndepFun W (fun ω k => O k ω) P)
    {G : ℕ → 𝒲 → Fin p → ℝ} (hG : ∀ n, Measurable (G n))
    (htm : TendstoInMeasure P (fun n ω => G n (W ω)) atTop (fun _ => t))
    (hq : 0 < T.μ.real (T.A ⁻¹' {a})) {m : 𝒳 → ℝ} (hm : T.IsCondMean a m)
    (hres2 : Integrable (fun ω => (T.Y a ω - m (T.X ω)) ^ 2) T.μ) {σ2 : ℝ}
    (hvar : T.μ[fun ω => (T.Y a ω - m (T.X ω)) ^ 2 | MeasurableSpace.comap T.X inferInstance]
      ≤ᵐ[T.μ] fun _ => σ2)
    {a0 : ℝ} {b : Fin p → ℝ} (haff : ∀ x, m x = a0 + b ⬝ᵥ φ x)
    {Q : Population Ω' 𝒳 ι} [IsProbabilityMeasure Q.μ] (hQX : Measurable Q.X)
    (hQφ : ∀ k, Integrable (fun x => φ x k) Q.covLaw) (ht : ∀ k, ∫ x, φ x k ∂Q.covLaw = t k)
    {ta : ι} (hQY : Integrable (Q.Y ta) Q.μ) (hQm : Q.IsCondMean ta m) :
    IsConsistent (fun n ω => sampleBalancedArmMean φ (G n (W ω)) O a n ω) (Q.armMean ta) P := by
  have : IsProbabilityMeasure Q.covLaw := Q.isProbabilityMeasure_covLaw hQX
  rw [← hQm.integral_eq hQX hQY, show m = fun x => a0 + b ⬝ᵥ φ x from funext haff,
    integral_affine_features_of_integrable hQφ ht a0 b]
  exact sampleBalancedArmMean_isConsistent_trial_general hX hA hYo a hYa hrand hO hOm hlaw hφ
    hint hexp hW hWO hG htm hq hm hres2 hvar haff

omit [MeasurableSpace 𝒳] in
/-- The observed outcome of a two arm trial is measurable when the assignment and both potential
outcomes are. -/
theorem measurable_obsOutcome_bool (hA : Measurable T.A) (hYt : Measurable (T.Y true))
    (hYf : Measurable (T.Y false)) : Measurable T.obsOutcome := by
  have h : T.obsOutcome = fun ω => if T.A ω = true then T.Y true ω else T.Y false ω := by
    funext ω
    simp only [Trial.obsOutcome]
    cases T.A ω <;> rfl
  rw [h]
  exact Measurable.ite (hA (measurableSet_singleton true)) hYt hYf

/-- **The unanchored weighted comparison, composed with unanchored identification.** Let `S` be
an unanchored setting satisfying the identification assumptions for the surfaces `m_a` and
`m_b`, and let the index trial `T`, with arm `true` standing for the treatment `S.a` of the
first source, satisfy the hypotheses of `sampleBalancedArmMean_isConsistent_trial_general` for
the surface `m_a = a₀ + bᵀφ`, with features of the target population integrable with means `t`.
If `m̂_B` is consistent for `∫ m_b dQ_X` (the reported mean of `S.b`) and `g` is continuous at
the target means, then `g(m̂_B) - g(μ̂_true)` at the targets `tₙ` is consistent for the target
effect `g(E_Q[Y(b)]) - g(E_Q[Y(a)])`. The identification theorem is used for its target side
conclusions: `m_a` is a conditional mean function in the target and `∫ m_b dQ_X = E_Q[Y(b)]`;
the index trial `T` is linked to the setting only through the surface `m_a`. -/
theorem unanchoredBalancedEstimate_isConsistent_trial {Ω₂ Ω₃ ι : Type*} [MeasurableSpace Ω₂]
    [MeasurableSpace Ω₃] {S : IndirectComparison.UnanchoredSetting Ω₁ Ω₂ Ω₃ 𝒳 ι}
    [IsFiniteMeasure S.sourceA.μ] [IsFiniteMeasure S.sourceB.μ]
    [IsProbabilityMeasure S.target.μ] {D : Set ℝ} {ma mb : 𝒳 → ℝ}
    (hS : S.IdentificationAssumptions D ma mb)
    (hX : Measurable T.X) (hA : Measurable T.A) (hYo : Measurable T.obsOutcome)
    (hYa : Measurable (T.Y true)) (hrand : IndepFun T.A (fun ω => (T.X ω, T.Y true ω)) T.μ)
    (hO : IsIIDSample O P) (hOm : ∀ i, Measurable (O i)) (hlaw : P.map (O 0) = T.ipdLaw)
    {φ : 𝒳 → Fin p → ℝ} (hφ : Measurable φ) {t : Fin p → ℝ}
    (hint : t ∈ interior (closedConvexHull ℝ (T.covLaw.map φ).support))
    (hexp : ∀ κ : ℝ, Integrable (fun x => Real.exp (κ * ‖φ x - t‖)) T.covLaw)
    {W : Ω → 𝒲} (hW : Measurable W) (hWO : IndepFun W (fun ω k => O k ω) P)
    {G : ℕ → 𝒲 → Fin p → ℝ} (hG : ∀ n, Measurable (G n))
    (htm : TendstoInMeasure P (fun n ω => G n (W ω)) atTop (fun _ => t))
    (hq : 0 < T.μ.real (T.A ⁻¹' {true})) (hm : T.IsCondMean true ma)
    (hres2 : Integrable (fun ω => (T.Y true ω - ma (T.X ω)) ^ 2) T.μ) {σ2 : ℝ}
    (hvar : T.μ[fun ω => (T.Y true ω - ma (T.X ω)) ^ 2 | MeasurableSpace.comap T.X
      inferInstance] ≤ᵐ[T.μ] fun _ => σ2)
    {a0 : ℝ} {b : Fin p → ℝ} (haff : ∀ x, ma x = a0 + b ⬝ᵥ φ x)
    (hQφ : ∀ k, Integrable (fun x => φ x k) S.target.covLaw)
    (ht : ∀ k, ∫ x, φ x k ∂S.target.covLaw = t k)
    {mB : ℕ → Ω → ℝ} (hmB : IsConsistent mB (∫ x, mb x ∂S.target.covLaw) P) {g : ℝ → ℝ}
    (hga : ContinuousAt g (S.target.armMean S.a)) (hgb : ContinuousAt g (S.target.armMean S.b)) :
    IsConsistent (fun n ω => g (mB n ω) - g (sampleBalancedArmMean φ (G n (W ω)) O true n ω))
      (S.target.marginalEffect g S.a S.b) P := by
  obtain ⟨hQa, -, -, -, -, -, hIb, -⟩ := hS.identification g
  have hArm := sampleBalancedArmMean_isConsistent_trial_armMean hX hA hYo true hYa hrand hO hOm
    hlaw hφ hint hexp hW hWO hG htm hq hm hres2 hvar haff hS.measurable_target hQφ ht
    hS.integrable_target_a hQa
  rw [hIb] at hmB
  exact (hmB.comp_continuousAt hgb).sub (hArm.comp_continuousAt hga)

/-- **The anchored weighted comparison.** Let both arms of the index trial `T` satisfy the
hypotheses of `sampleBalancedArmMean_isConsistent_trial_general` (arm `true` with surface
`m_A = a₀ + bᵀφ`, arm `false` with surface `m_C = c₀ + dᵀφ`), and let `Q` be a target
population with integrable features of means `t` in which `m_A` and `m_C` are conditional mean
functions of the integrable outcomes `Y(ta)` and `Y(tc)`. If `d̂_BC` is consistent for
`g(E_Q[Y(tc)]) - g(E_Q[Y(tb)])` and `g` is continuous at the target means of `ta` and `tc`,
then `(g(μ̂_false) - g(μ̂_true)) - d̂_BC` at the targets `tₙ` is consistent for the target
effect `g(E_Q[Y(tb)]) - g(E_Q[Y(ta)])`. -/
theorem anchoredBalancedEstimate_isConsistent_trial {Ω' ι : Type*} [MeasurableSpace Ω']
    (hX : Measurable T.X) (hA : Measurable T.A)
    (hYt : Measurable (T.Y true)) (hYf : Measurable (T.Y false))
    (hrt : IndepFun T.A (fun ω => (T.X ω, T.Y true ω)) T.μ)
    (hrf : IndepFun T.A (fun ω => (T.X ω, T.Y false ω)) T.μ)
    (hO : IsIIDSample O P) (hOm : ∀ i, Measurable (O i)) (hlaw : P.map (O 0) = T.ipdLaw)
    {φ : 𝒳 → Fin p → ℝ} (hφ : Measurable φ) {t : Fin p → ℝ}
    (hint : t ∈ interior (closedConvexHull ℝ (T.covLaw.map φ).support))
    (hexp : ∀ κ : ℝ, Integrable (fun x => Real.exp (κ * ‖φ x - t‖)) T.covLaw)
    {W : Ω → 𝒲} (hW : Measurable W) (hWO : IndepFun W (fun ω k => O k ω) P)
    {G : ℕ → 𝒲 → Fin p → ℝ} (hG : ∀ n, Measurable (G n))
    (htm : TendstoInMeasure P (fun n ω => G n (W ω)) atTop (fun _ => t))
    (hqt : 0 < T.μ.real (T.A ⁻¹' {true})) (hqf : 0 < T.μ.real (T.A ⁻¹' {false}))
    {mA mC : 𝒳 → ℝ} (hmA : T.IsCondMean true mA) (hmC : T.IsCondMean false mC)
    (hrA : Integrable (fun ω => (T.Y true ω - mA (T.X ω)) ^ 2) T.μ)
    (hrC : Integrable (fun ω => (T.Y false ω - mC (T.X ω)) ^ 2) T.μ) {σ2 : ℝ}
    (hvA : T.μ[fun ω => (T.Y true ω - mA (T.X ω)) ^ 2 | MeasurableSpace.comap T.X
      inferInstance] ≤ᵐ[T.μ] fun _ => σ2)
    (hvC : T.μ[fun ω => (T.Y false ω - mC (T.X ω)) ^ 2 | MeasurableSpace.comap T.X
      inferInstance] ≤ᵐ[T.μ] fun _ => σ2)
    {a0 c0 : ℝ} {b d : Fin p → ℝ} (hafA : ∀ x, mA x = a0 + b ⬝ᵥ φ x)
    (hafC : ∀ x, mC x = c0 + d ⬝ᵥ φ x)
    {Q : Population Ω' 𝒳 ι} [IsProbabilityMeasure Q.μ] (hQX : Measurable Q.X)
    (hQφ : ∀ k, Integrable (fun x => φ x k) Q.covLaw) (ht : ∀ k, ∫ x, φ x k ∂Q.covLaw = t k)
    {ta tb tc : ι} (hQa : Integrable (Q.Y ta) Q.μ) (hQc : Integrable (Q.Y tc) Q.μ)
    (hQmA : Q.IsCondMean ta mA) (hQmC : Q.IsCondMean tc mC) {dBC : ℕ → Ω → ℝ} {g : ℝ → ℝ}
    (hd : IsConsistent dBC (g (Q.armMean tc) - g (Q.armMean tb)) P)
    (hga : ContinuousAt g (Q.armMean ta)) (hgc : ContinuousAt g (Q.armMean tc)) :
    IsConsistent (fun n ω => (g (sampleBalancedArmMean φ (G n (W ω)) O false n ω) -
        g (sampleBalancedArmMean φ (G n (W ω)) O true n ω)) - dBC n ω)
      (Q.marginalEffect g ta tb) P := by
  have hYo := measurable_obsOutcome_bool hA hYt hYf
  have h1 := sampleBalancedArmMean_isConsistent_trial_armMean hX hA hYo true hYt hrt hO hOm
    hlaw hφ hint hexp hW hWO hG htm hqt hmA hrA hvA hafA hQX hQφ ht hQa hQmA
  have h2 := sampleBalancedArmMean_isConsistent_trial_armMean hX hA hYo false hYf hrf hO hOm
    hlaw hφ hint hexp hW hWO hG htm hqf hmC hrC hvC hafC hQX hQφ ht hQc hQmC
  have h := ((h2.comp_continuousAt hgc).sub (h1.comp_continuousAt hga)).sub hd
  have he : g (Q.armMean tc) - g (Q.armMean ta) - (g (Q.armMean tc) - g (Q.armMean tb)) =
      Q.marginalEffect g ta tb := by
    rw [Population.marginalEffect]; ring
  rw [IsConsistent, ← he]
  exact h

/-- **The anchored weighted comparison on the identity scale, composed with anchored
identification.** Let `S` be an anchored setting satisfying the identification assumptions on
the identity scale (domain `ℝ`) for the surfaces `m₁` (first trial), `m₂` (second trial) and `m`
(target). Let both arms of the index trial `T`, arm `true` with surface `m₁ S.a = a₀ + bᵀφ` and
arm `false` with surface `m₁ S.c = c₀ + dᵀφ`, satisfy the hypotheses of
`sampleBalancedArmMean_isConsistent_trial_general`, with features of the target population
integrable with means `t`. If `d̂_BC` is consistent for the target average of the contrast of the
second trial, `∫ (m₂ c - m₂ b) dQ_X`, then `(μ̂_false - μ̂_true) - d̂_BC` at the targets `tₙ` is
consistent for the anchored estimand, which is the target effect `E_Q[Y(b)] - E_Q[Y(a)]`
(identity scale, directly collapsible). The index trial is linked to the setting through the
surfaces `m₁ S.a` and `m₁ S.c`. -/
theorem anchoredBalancedEstimate_isConsistent_identity_trial {Ω₂ Ω₃ ι : Type*}
    [MeasurableSpace Ω₂] [MeasurableSpace Ω₃] {S : IndirectComparison.AnchoredSetting Ω₁ Ω₂ Ω₃ 𝒳 ι}
    [IsFiniteMeasure S.ipdTrial.μ] [IsFiniteMeasure S.agdTrial.μ]
    [IsProbabilityMeasure S.target.μ] {m₁ m₂ m : ι → 𝒳 → ℝ}
    (hS : S.IdentificationAssumptions id Set.univ m₁ m₂ m)
    (hX : Measurable T.X) (hA : Measurable T.A)
    (hYt : Measurable (T.Y true)) (hYf : Measurable (T.Y false))
    (hrt : IndepFun T.A (fun ω => (T.X ω, T.Y true ω)) T.μ)
    (hrf : IndepFun T.A (fun ω => (T.X ω, T.Y false ω)) T.μ)
    (hO : IsIIDSample O P) (hOm : ∀ i, Measurable (O i)) (hlaw : P.map (O 0) = T.ipdLaw)
    {φ : 𝒳 → Fin p → ℝ} (hφ : Measurable φ) {t : Fin p → ℝ}
    (hint : t ∈ interior (closedConvexHull ℝ (T.covLaw.map φ).support))
    (hexp : ∀ κ : ℝ, Integrable (fun x => Real.exp (κ * ‖φ x - t‖)) T.covLaw)
    {W : Ω → 𝒲} (hW : Measurable W) (hWO : IndepFun W (fun ω k => O k ω) P)
    {G : ℕ → 𝒲 → Fin p → ℝ} (hG : ∀ n, Measurable (G n))
    (htm : TendstoInMeasure P (fun n ω => G n (W ω)) atTop (fun _ => t))
    (hqt : 0 < T.μ.real (T.A ⁻¹' {true})) (hqf : 0 < T.μ.real (T.A ⁻¹' {false}))
    (hmA : T.IsCondMean true (m₁ S.a)) (hmC : T.IsCondMean false (m₁ S.c))
    (hrA : Integrable (fun ω => (T.Y true ω - m₁ S.a (T.X ω)) ^ 2) T.μ)
    (hrC : Integrable (fun ω => (T.Y false ω - m₁ S.c (T.X ω)) ^ 2) T.μ) {σ2 : ℝ}
    (hvA : T.μ[fun ω => (T.Y true ω - m₁ S.a (T.X ω)) ^ 2 | MeasurableSpace.comap T.X
      inferInstance] ≤ᵐ[T.μ] fun _ => σ2)
    (hvC : T.μ[fun ω => (T.Y false ω - m₁ S.c (T.X ω)) ^ 2 | MeasurableSpace.comap T.X
      inferInstance] ≤ᵐ[T.μ] fun _ => σ2)
    {a0 c0 : ℝ} {b d : Fin p → ℝ} (hafA : ∀ x, m₁ S.a x = a0 + b ⬝ᵥ φ x)
    (hafC : ∀ x, m₁ S.c x = c0 + d ⬝ᵥ φ x)
    (hQφ : ∀ k, Integrable (fun x => φ x k) S.target.covLaw)
    (ht : ∀ k, ∫ x, φ x k ∂S.target.covLaw = t k) {dBC : ℕ → Ω → ℝ}
    (hd : IsConsistent dBC (∫ x, linkContrast id (m₂ S.b) (m₂ S.c) x ∂S.target.covLaw) P) :
    IsConsistent (fun n ω => (sampleBalancedArmMean φ (G n (W ω)) O false n ω -
        sampleBalancedArmMean φ (G n (W ω)) O true n ω) - dBC n ω)
      (S.target.marginalEffect id S.a S.b) P := by
  have hYo := measurable_obsOutcome_bool hA hYt hYf
  have : IsProbabilityMeasure S.target.covLaw :=
    S.target.isProbabilityMeasure_covLaw hS.measurable_target
  have h1 := sampleBalancedArmMean_isConsistent_trial_general hX hA hYo true hYt hrt hO hOm
    hlaw hφ hint hexp hW hWO hG htm hqt hmA hrA hvA hafA
  have h2 := sampleBalancedArmMean_isConsistent_trial_general hX hA hYo false hYf hrf hO hOm
    hlaw hφ hint hexp hW hWO hG htm hqf hmC hrC hvC hafC
  have hEA : ∫ x, m₁ S.a x ∂S.target.covLaw = a0 + b ⬝ᵥ t := by
    rw [show m₁ S.a = fun x => a0 + b ⬝ᵥ φ x from funext hafA]
    exact integral_affine_features_of_integrable hQφ ht a0 b
  have hEC : ∫ x, m₁ S.c x ∂S.target.covLaw = c0 + d ⬝ᵥ t := by
    rw [show m₁ S.c = fun x => c0 + d ⬝ᵥ φ x from funext hafC]
    exact integral_affine_features_of_integrable hQφ ht c0 d
  have hiA : Integrable (m₁ S.a) S.target.covLaw := by
    rw [show m₁ S.a = fun x => a0 + b ⬝ᵥ φ x from funext hafA]
    exact (integrable_const a0).add (integrable_finsetSum _ fun k _ => (hQφ k).const_mul (b k))
  have hiC : Integrable (m₁ S.c) S.target.covLaw := by
    rw [show m₁ S.c = fun x => c0 + d ⬝ᵥ φ x from funext hafC]
    exact (integrable_const c0).add (integrable_finsetSum _ fun k _ => (hQφ k).const_mul (d k))
  have hest : anchoredEstimand S.target.covLaw (linkContrast id (m₁ S.a) (m₁ S.c))
      (linkContrast id (m₂ S.b) (m₂ S.c)) = (c0 + d ⬝ᵥ t - (a0 + b ⬝ᵥ t)) -
        ∫ x, linkContrast id (m₂ S.b) (m₂ S.c) x ∂S.target.covLaw := by
    rw [anchoredEstimand]
    congr 1
    simp only [linkContrast, id]
    rw [integral_sub hiC hiA, hEA, hEC]
  have heff := (hS.anchoredEstimand_eq_marginalEffect measurable_id MeasurableSet.univ
    (Or.inl linkDirectlyCollapsible_id)).2
  rw [hest] at heff
  rw [IsConsistent, ← heff]
  exact (h2.sub h1).sub hd

end Consistency

end PopulationAdjustment

end CausalInference
