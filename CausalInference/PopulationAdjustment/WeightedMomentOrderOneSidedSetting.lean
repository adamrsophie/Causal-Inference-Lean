/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.PopulationAdjustment.WeightedMomentOrderSetting
public import CausalInference.PopulationAdjustment.WeightedMomentOrderOneSided

/-!
# The weighted estimator of a setting under one sided moments

The consistency theorems for an index trial and for the trial of an anchored or unanchored
setting under one exponential moment
(`sampleBalancedArmMean_isConsistent_trial_armMean_of_isMinOn`,
`unanchoredBalancedEstimate_isConsistent_trial_of_isMinOn`,
`anchoredBalancedEstimate_isConsistent_identity_trial_of_isMinOn`,
`anchoredWeightedEstimate_isConsistent_setting_of_isMinOn`,
`unanchoredWeightedEstimate_isConsistent_setting_of_isMinOn`) assume
`E[exp(κ ‖φ(X) - t‖)] < ∞` for one `κ > 2 p ‖β*‖`, where `β*` minimizes the population dual
objective `E[exp(βᵀ(φ(X) - t))]` of the trial covariate law. Here this moment is replaced by the
two one sided conditions of `sampleBalancedArmMean_isConsistent_trial_of_isMinOn_oneSided`:

* a norm moment `E[exp(r ‖φ(X) - t‖)] < ∞` of some order `r > 0`, and
* the directional moment `E[exp(2 (1 + ε) β*ᵀ(φ(X) - t))] < ∞` for some `ε > 0`.

The outcome side is unchanged: for each arm used, a square integrable residual `Y(s) - m(X)` with
bounded conditional variance; the target side asks for integrable features with means `t`. Each
theorem is derived from the arm level statement
`sampleBalancedArmMean_isConsistent_trial_of_isMinOn_oneSided`.

## Main results

* `sampleBalancedArmMean_isConsistent_trial_armMean_of_isMinOn_oneSided`: the limit is the target
  arm mean.
* `unanchoredBalancedEstimate_isConsistent_trial_of_isMinOn_oneSided`,
  `anchoredBalancedEstimate_isConsistent_identity_trial_of_isMinOn_oneSided`: an index trial.
* `anchoredWeightedEstimate_isConsistent_setting_of_isMinOn_oneSided`,
  `unanchoredWeightedEstimate_isConsistent_setting_of_isMinOn_oneSided`: the trial of the setting.

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

/-! ### An index trial -/

section Trial

variable {Ω₁ Ω 𝒳 𝒲 : Type*} [MeasurableSpace Ω₁] [MeasurableSpace Ω] [MeasurableSpace 𝒳]
  [MeasurableSpace 𝒲] {p : ℕ} {T : Trial Ω₁ 𝒳 Bool} {P : Measure Ω} [IsProbabilityMeasure P]
  {O : ℕ → Ω → 𝒳 × Bool × ℝ}

/-- **The limit is the target arm mean, under one sided moments.** Under the hypotheses of
`sampleBalancedArmMean_isConsistent_trial_of_isMinOn_oneSided` (the interior condition, a
minimizer `β*` of the population dual objective of the trial covariate law,
`E[exp(r ‖φ(X) - t‖)] < ∞` for some `r > 0` and `E[exp(2 (1 + ε) β*ᵀ(φ(X) - t))] < ∞` for some
`ε > 0`), let `Q` be a target population whose features are integrable with means
`t` and in which `m` is a conditional mean function of the integrable outcome `Y(s)`. Then the
weighted arm mean at the targets `tₙ` is consistent for the target arm mean `E_Q[Y(s)]`. -/
theorem sampleBalancedArmMean_isConsistent_trial_armMean_of_isMinOn_oneSided {Ω' ι : Type*}
    [MeasurableSpace Ω'] (hX : Measurable T.X)
    (hA : Measurable T.A) (hYo : Measurable T.obsOutcome) (a : Bool)
    (hYa : Measurable (T.Y a)) (hrand : IndepFun T.A (fun ω => (T.X ω, T.Y a ω)) T.μ)
    (hO : IsIIDSample O P) (hOm : ∀ i, Measurable (O i)) (hlaw : P.map (O 0) = T.ipdLaw)
    {φ : 𝒳 → Fin p → ℝ} (hφ : Measurable φ) {t : Fin p → ℝ}
    (hint : t ∈ interior (closedConvexHull ℝ (T.covLaw.map φ).support))
    {βs : Fin p → ℝ} (hmin : IsMinOn (sharpDualObjective T.covLaw φ t) Set.univ βs)
    {r : ℝ} (hr : 0 < r) (hexp : Integrable (fun x => Real.exp (r * ‖φ x - t‖)) T.covLaw)
    {ε : ℝ} (hε : 0 < ε)
    (hdir : Integrable (fun x => Real.exp (2 * (1 + ε) * (βs ⬝ᵥ (φ x - t)))) T.covLaw)
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
    {s : ι} (hQY : Integrable (Q.Y s) Q.μ) (hQm : Q.IsCondMean s m) :
    IsConsistent (fun n ω => sampleBalancedArmMean φ (G n (W ω)) O a n ω) (Q.armMean s) P := by
  have : IsProbabilityMeasure Q.covLaw := Q.isProbabilityMeasure_covLaw hQX
  rw [← hQm.integral_eq hQX hQY, show m = fun x => a0 + b ⬝ᵥ φ x from funext haff,
    integral_affine_features_of_integrable hQφ ht a0 b]
  exact sampleBalancedArmMean_isConsistent_trial_of_isMinOn_oneSided hX hA hYo a hYa hrand hO hOm
    hlaw hφ hint hmin hr hexp hε hdir hW hWO hG htm hq hm hres2 hvar haff

/-- **The unanchored weighted comparison under one sided moments.** Let `S` be an unanchored
setting satisfying the identification assumptions for the surfaces `m_a` and `m_b`, and let arm
`true` of the index trial `T` satisfy the hypotheses of
`sampleBalancedArmMean_isConsistent_trial_of_isMinOn_oneSided` for the surface `m_a = a₀ + bᵀφ` (a
norm moment of some order `r > 0` and the directional moment of order `2 (1 + ε)` along `β*`),
with target features integrable with means `t`. If `m̂_B` is consistent for `∫ m_b dQ_X` and `g`
is continuous at the target means, then `g(m̂_B) - g(μ̂_true)` at the targets `tₙ` is consistent
for `g(E_Q[Y(b)]) - g(E_Q[Y(a)])`. -/
theorem unanchoredBalancedEstimate_isConsistent_trial_of_isMinOn_oneSided {Ω₂ Ω₃ ι : Type*}
    [MeasurableSpace Ω₂] [MeasurableSpace Ω₃] {S : UnanchoredSetting Ω₁ Ω₂ Ω₃ 𝒳 ι}
    [IsFiniteMeasure S.sourceA.μ] [IsFiniteMeasure S.sourceB.μ]
    [IsProbabilityMeasure S.target.μ] {D : Set ℝ} {ma mb : 𝒳 → ℝ}
    (hS : S.IdentificationAssumptions D ma mb)
    (hX : Measurable T.X) (hA : Measurable T.A) (hYo : Measurable T.obsOutcome)
    (hYa : Measurable (T.Y true)) (hrand : IndepFun T.A (fun ω => (T.X ω, T.Y true ω)) T.μ)
    (hO : IsIIDSample O P) (hOm : ∀ i, Measurable (O i)) (hlaw : P.map (O 0) = T.ipdLaw)
    {φ : 𝒳 → Fin p → ℝ} (hφ : Measurable φ) {t : Fin p → ℝ}
    (hint : t ∈ interior (closedConvexHull ℝ (T.covLaw.map φ).support))
    {βs : Fin p → ℝ} (hmin : IsMinOn (sharpDualObjective T.covLaw φ t) Set.univ βs)
    {r : ℝ} (hr : 0 < r) (hexp : Integrable (fun x => Real.exp (r * ‖φ x - t‖)) T.covLaw)
    {ε : ℝ} (hε : 0 < ε)
    (hdir : Integrable (fun x => Real.exp (2 * (1 + ε) * (βs ⬝ᵥ (φ x - t)))) T.covLaw)
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
  have hArm := sampleBalancedArmMean_isConsistent_trial_armMean_of_isMinOn_oneSided hX hA hYo true
    hYa hrand hO hOm hlaw hφ hint hmin hr hexp hε hdir hW hWO hG htm hq hm hres2 hvar haff
    hS.measurable_target hQφ ht hS.integrable_target_a hQa
  rw [hIb] at hmB
  exact (hmB.comp_continuousAt hgb).sub (hArm.comp_continuousAt hga)

/-- **The anchored weighted comparison on the identity scale under one sided moments.** Let
`S` be an anchored setting satisfying the identification assumptions on the identity scale for
the surfaces `m₁`, `m₂`, `m`, and let both arms of the index trial `T` (arm `true` with surface
`m₁ S.a = a₀ + bᵀφ`, arm `false` with `m₁ S.c = c₀ + dᵀφ`) satisfy the hypotheses of
`sampleBalancedArmMean_isConsistent_trial_of_isMinOn_oneSided`. The two arms share the covariate
law, so one minimizer `β*`, one norm moment of order `r > 0` and one directional moment serve
both. With target features
integrable with means `t` and `d̂_BC` consistent for `∫ (m₂ c - m₂ b) dQ_X`, the comparison
`(μ̂_false - μ̂_true) - d̂_BC` at the targets `tₙ` is consistent for `E_Q[Y(b)] - E_Q[Y(a)]`. -/
theorem anchoredBalancedEstimate_isConsistent_identity_trial_of_isMinOn_oneSided
    {Ω₂ Ω₃ ι : Type*} [MeasurableSpace Ω₂] [MeasurableSpace Ω₃] {S : AnchoredSetting Ω₁ Ω₂ Ω₃ 𝒳 ι}
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
    {βs : Fin p → ℝ} (hmin : IsMinOn (sharpDualObjective T.covLaw φ t) Set.univ βs)
    {r : ℝ} (hr : 0 < r) (hexp : Integrable (fun x => Real.exp (r * ‖φ x - t‖)) T.covLaw)
    {ε : ℝ} (hε : 0 < ε)
    (hdir : Integrable (fun x => Real.exp (2 * (1 + ε) * (βs ⬝ᵥ (φ x - t)))) T.covLaw)
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
  have h1 := sampleBalancedArmMean_isConsistent_trial_of_isMinOn_oneSided hX hA hYo true hYt hrt hO
    hOm hlaw hφ hint hmin hr hexp hε hdir hW hWO hG htm hqt hmA hrA hvA hafA
  have h2 := sampleBalancedArmMean_isConsistent_trial_of_isMinOn_oneSided hX hA hYo false hYf hrf hO
    hOm hlaw hφ hint hmin hr hexp hε hdir hW hWO hG htm hqf hmC hrC hvC hafC
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

end Trial

/-! ### The trial of the setting -/

section Setting

variable {Ω₁ Ω₂ Ω₃ Ω 𝒳 ι 𝒲 : Type*} [MeasurableSpace Ω₁] [MeasurableSpace Ω₂]
  [MeasurableSpace Ω₃] [MeasurableSpace Ω] [MeasurableSpace 𝒳] [MeasurableSpace ι]
  [MeasurableSingletonClass ι] [DecidableEq ι] [MeasurableSpace 𝒲] {p : ℕ}
  {P : Measure Ω} [IsProbabilityMeasure P]

/-- **The anchored weighted estimate for the trial of the setting under one sided moments.** The
hypotheses of `anchoredWeightedEstimate_isConsistent_setting_of_isMinOn`, with the moment of
order `κ > 2 p ‖β*‖` replaced by `E[exp(r ‖φ(X) - t‖)] < ∞` for some `r > 0` and
`E[exp(2 (1 + ε) β*ᵀ(φ(X) - t))] < ∞` for some `ε > 0`, both under the covariate law of the
individual data trial, where `β*` minimizes its population dual objective `E[exp(βᵀ(φ(X) - t))]`.
The outcome side needs, for each of the two treatments `s ∈ {a, c}`, a square integrable residual
`Y(s) - m₁ s (X)` with conditional variance at most `σ²`. Then the
anchored weighted estimate `(μ̂_c - μ̂_a) - d̂_bc`, with the entropy balancing weights at the
reported targets `tₙ` and the treatment labels of the records, is consistent for
`E_Q[Y(b)] - E_Q[Y(a)]`. -/
theorem anchoredWeightedEstimate_isConsistent_setting_of_isMinOn_oneSided
    {S : AnchoredSetting Ω₁ Ω₂ Ω₃ 𝒳 ι}
    [IsFiniteMeasure S.ipdTrial.μ] [IsFiniteMeasure S.agdTrial.μ]
    [IsProbabilityMeasure S.target.μ] {m₁ m₂ m : ι → 𝒳 → ℝ}
    (hS : S.IdentificationAssumptions id Set.univ m₁ m₂ m) (hac : S.a ≠ S.c)
    (hA : Measurable S.ipdTrial.A) (hYa : Measurable (S.ipdTrial.Y S.a))
    (hYc : Measurable (S.ipdTrial.Y S.c))
    (hAac : ∀ᵐ ω ∂S.ipdTrial.μ, S.ipdTrial.A ω = S.a ∨ S.ipdTrial.A ω = S.c)
    (hra : IndepFun S.ipdTrial.A (fun ω => (S.ipdTrial.X ω, S.ipdTrial.Y S.a ω)) S.ipdTrial.μ)
    (hrc : IndepFun S.ipdTrial.A (fun ω => (S.ipdTrial.X ω, S.ipdTrial.Y S.c ω)) S.ipdTrial.μ)
    (hqa : 0 < S.ipdTrial.μ.real (S.ipdTrial.A ⁻¹' {S.a}))
    (hqc : 0 < S.ipdTrial.μ.real (S.ipdTrial.A ⁻¹' {S.c}))
    {R : ℕ → Ω → 𝒳 × ι × ℝ} (hR : IsIIDSample R P) (hRm : ∀ i, Measurable (R i))
    (hlaw : P.map (R 0) = S.ipdTrial.ipdLaw)
    {φ : 𝒳 → Fin p → ℝ} (hφ : Measurable φ) {t : Fin p → ℝ}
    (hint : t ∈ interior (closedConvexHull ℝ (S.ipdTrial.covLaw.map φ).support))
    {βs : Fin p → ℝ} (hmin : IsMinOn (sharpDualObjective S.ipdTrial.covLaw φ t) Set.univ βs)
    {r : ℝ} (hr : 0 < r)
    (hexp : Integrable (fun x => Real.exp (r * ‖φ x - t‖)) S.ipdTrial.covLaw)
    {ε : ℝ} (hε : 0 < ε)
    (hdir : Integrable (fun x => Real.exp (2 * (1 + ε) * (βs ⬝ᵥ (φ x - t)))) S.ipdTrial.covLaw)
    {W : Ω → 𝒲} (hW : Measurable W) (hWR : IndepFun W (fun ω k => R k ω) P)
    {G : ℕ → 𝒲 → Fin p → ℝ} (hG : ∀ n, Measurable (G n))
    (htm : TendstoInMeasure P (fun n ω => G n (W ω)) atTop (fun _ => t))
    (hrA : Integrable (fun ω => (S.ipdTrial.Y S.a ω - m₁ S.a (S.ipdTrial.X ω)) ^ 2)
      S.ipdTrial.μ)
    (hrC : Integrable (fun ω => (S.ipdTrial.Y S.c ω - m₁ S.c (S.ipdTrial.X ω)) ^ 2)
      S.ipdTrial.μ) {σ2 : ℝ}
    (hvA : S.ipdTrial.μ[fun ω => (S.ipdTrial.Y S.a ω - m₁ S.a (S.ipdTrial.X ω)) ^ 2 |
      MeasurableSpace.comap S.ipdTrial.X inferInstance] ≤ᵐ[S.ipdTrial.μ] fun _ => σ2)
    (hvC : S.ipdTrial.μ[fun ω => (S.ipdTrial.Y S.c ω - m₁ S.c (S.ipdTrial.X ω)) ^ 2 |
      MeasurableSpace.comap S.ipdTrial.X inferInstance] ≤ᵐ[S.ipdTrial.μ] fun _ => σ2)
    {a0 c0 : ℝ} {b d : Fin p → ℝ} (hafA : ∀ x, m₁ S.a x = a0 + b ⬝ᵥ φ x)
    (hafC : ∀ x, m₁ S.c x = c0 + d ⬝ᵥ φ x)
    (hQφ : ∀ k, Integrable (fun x => φ x k) S.target.covLaw)
    (ht : ∀ k, ∫ x, φ x k ∂S.target.covLaw = t k) {dBC : ℕ → Ω → ℝ}
    (hd : IsConsistent dBC (∫ x, linkContrast id (m₂ S.b) (m₂ S.c) x ∂S.target.covLaw) P) :
    IsConsistent (fun n => anchoredWeightedEstimate id
        (fun ω => balancingWeights fun i : Fin n => φ (R i ω).1 - G n (W ω))
        (fun ω i => (R i ω).2.1) (fun ω i => (R i ω).2.2) S.a S.c (dBC n))
      (S.target.marginalEffect id S.a S.b) P := by
  have hX := hS.measurable_ipd
  obtain ⟨hR', hR'm, hlaw', hae⟩ :=
    S.ipdTrial.isIIDSample_twoArmRecord hac hX hA hYa hYc hAac hR hRm hlaw
  have hWR' : IndepFun W (fun ω k => twoArmRecord S.a (R k ω)) P :=
    hWR.comp measurable_id
      (Measurable.of_eval fun k => (measurable_twoArmRecord S.a).comp (measurable_pi_apply k))
  have h := anchoredBalancedEstimate_isConsistent_identity_trial_of_isMinOn_oneSided
    (T := S.ipdTrial.twoArmView S.a S.c) hS hX (S.ipdTrial.measurable_twoArmView_A hA _ _)
    hYa hYc (S.ipdTrial.indepFun_twoArmView_true _ _ hra)
    (S.ipdTrial.indepFun_twoArmView_false _ _ hrc) hR' hR'm hlaw' hφ hint hmin hr hexp hε hdir hW
    hWR' hG htm (by rw [Trial.twoArmView_prob_true]; exact hqa)
    (S.ipdTrial.twoArmView_prob_false_pos hac hqc) hS.isCondMean_ipd_a hS.isCondMean_ipd_c
    hrA hrC hvA hvC hafA hafC hQφ ht hd
  refine TendstoInMeasure.congr' (Eventually.of_forall fun n => hae.mono fun ω hω => ?_)
    EventuallyEq.rfl h
  rw [anchoredWeightedEstimate_eq, sampleBalancedArmMean_twoArmRecord_true,
    sampleBalancedArmMean_twoArmRecord_false φ _ R hac n ω hω]
  rfl

/-- **The unanchored weighted comparison when the source of `a` is a randomized trial, under one
sided moments.** The hypotheses of `unanchoredWeightedEstimate_isConsistent_setting_of_isMinOn`,
with the moment of order `κ > 2 p ‖β*‖` replaced by `E[exp(r ‖φ(X) - t‖)] < ∞` for some `r > 0`
and `E[exp(2 (1 + ε) β*ᵀ(φ(X) - t))] < ∞` for some `ε > 0`, both under the covariate law of the
trial `T`. The outcome side needs a square integrable residual `Y(a) - m_a(X)` with
conditional variance at most `σ²`. Then `g(m̂_b) - g(μ̂_a)`, with `μ̂_a` the weighted mean of the
treatment `a` of the records with their own labels, is consistent for
`g(E_Q[Y(b)]) - g(E_Q[Y(a)])`. -/
theorem unanchoredWeightedEstimate_isConsistent_setting_of_isMinOn_oneSided
    {S : UnanchoredSetting Ω₁ Ω₂ Ω₃ 𝒳 ι}
    [IsFiniteMeasure S.sourceA.μ] [IsFiniteMeasure S.sourceB.μ]
    [IsProbabilityMeasure S.target.μ] {D : Set ℝ} {ma mb : 𝒳 → ℝ}
    (hS : S.IdentificationAssumptions D ma mb) {T : Trial Ω₁ 𝒳 ι}
    (hsrc : T.toPopulation = S.sourceA) {c : ι} (hac : S.a ≠ c)
    (hA : Measurable T.A) (hYa : Measurable (T.Y S.a)) (hYc : Measurable (T.Y c))
    (hAac : ∀ᵐ ω ∂T.μ, T.A ω = S.a ∨ T.A ω = c)
    (hra : IndepFun T.A (fun ω => (T.X ω, T.Y S.a ω)) T.μ)
    (hqa : 0 < T.μ.real (T.A ⁻¹' {S.a}))
    {R : ℕ → Ω → 𝒳 × ι × ℝ} (hR : IsIIDSample R P) (hRm : ∀ i, Measurable (R i))
    (hlaw : P.map (R 0) = T.ipdLaw)
    {φ : 𝒳 → Fin p → ℝ} (hφ : Measurable φ) {t : Fin p → ℝ}
    (hint : t ∈ interior (closedConvexHull ℝ (T.covLaw.map φ).support))
    {βs : Fin p → ℝ} (hmin : IsMinOn (sharpDualObjective T.covLaw φ t) Set.univ βs)
    {r : ℝ} (hr : 0 < r) (hexp : Integrable (fun x => Real.exp (r * ‖φ x - t‖)) T.covLaw)
    {ε : ℝ} (hε : 0 < ε)
    (hdir : Integrable (fun x => Real.exp (2 * (1 + ε) * (βs ⬝ᵥ (φ x - t)))) T.covLaw)
    {W : Ω → 𝒲} (hW : Measurable W) (hWR : IndepFun W (fun ω k => R k ω) P)
    {G : ℕ → 𝒲 → Fin p → ℝ} (hG : ∀ n, Measurable (G n))
    (htm : TendstoInMeasure P (fun n ω => G n (W ω)) atTop (fun _ => t))
    (hres2 : Integrable (fun ω => (T.Y S.a ω - ma (T.X ω)) ^ 2) T.μ) {σ2 : ℝ}
    (hvar : T.μ[fun ω => (T.Y S.a ω - ma (T.X ω)) ^ 2 | MeasurableSpace.comap T.X
      inferInstance] ≤ᵐ[T.μ] fun _ => σ2)
    {a0 : ℝ} {b : Fin p → ℝ} (haff : ∀ x, ma x = a0 + b ⬝ᵥ φ x)
    (hQφ : ∀ k, Integrable (fun x => φ x k) S.target.covLaw)
    (ht : ∀ k, ∫ x, φ x k ∂S.target.covLaw = t k)
    {mB : ℕ → Ω → ℝ} (hmB : IsConsistent mB (∫ x, mb x ∂S.target.covLaw) P) {g : ℝ → ℝ}
    (hga : ContinuousAt g (S.target.armMean S.a)) (hgb : ContinuousAt g (S.target.armMean S.b)) :
    IsConsistent (fun n ω => g (mB n ω) - g (weightedArmMean
        (balancingWeights fun i : Fin n => φ (R i ω).1 - G n (W ω))
        (fun i => (R i ω).2.1) (fun i => (R i ω).2.2) S.a))
      (S.target.marginalEffect g S.a S.b) P := by
  have hX : Measurable T.X := by
    have := hS.measurable_sourceA
    rw [← hsrc] at this
    exact this
  have hm : (T.twoArmView S.a c).IsCondMean true ma := by
    rw [Trial.twoArmView_isCondMean_true, hsrc]
    exact hS.isCondMean_a
  obtain ⟨hR', hR'm, hlaw', -⟩ := T.isIIDSample_twoArmRecord hac hX hA hYa hYc hAac hR hRm hlaw
  have hWR' : IndepFun W (fun ω k => twoArmRecord S.a (R k ω)) P :=
    hWR.comp measurable_id
      (Measurable.of_eval fun k => (measurable_twoArmRecord S.a).comp (measurable_pi_apply k))
  have hA' := T.measurable_twoArmView_A hA S.a c
  have h := unanchoredBalancedEstimate_isConsistent_trial_of_isMinOn_oneSided
    (T := T.twoArmView S.a c)
    hS hX hA' (measurable_obsOutcome_bool hA' hYa hYc) hYa (T.indepFun_twoArmView_true _ _ hra)
    hR' hR'm hlaw' hφ hint hmin hr hexp hε hdir hW hWR' hG htm
    (by rw [Trial.twoArmView_prob_true]; exact hqa) hm hres2 hvar haff hQφ ht hmB hga hgb
  simp only [sampleBalancedArmMean_twoArmRecord_true] at h
  exact h

end Setting

end PopulationAdjustment

end CausalInference
