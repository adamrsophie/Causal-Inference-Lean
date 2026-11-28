/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.NetworkMetaRegression.UnanchoredIdentification
public import CausalInference.Estimation.ConvergenceInProbability
public import CausalInference.PopulationAdjustment.UnanchoredIdentification

/-!
# Consistency of the unanchored standardized comparison

Under shared prognostic effects the unanchored estimand is the plug in

`Φ(α, β, θ) = g(∫ g⁻¹(c(β, θ) + xᵀβ) dQ) - g(∫ g⁻¹(α + xᵀβ) dQ)`

of the cell intercept `α` and cell slope `β` of `a` (from the individual data) and the aggregate
mean `θ` of `b`, with `c(β, θ)` the calibrated shift under the covariate law `F_B` of the
aggregate study (`unanchored_estimand_eq_calibrated`). This file shows that `Φ` is continuous at
the true parameters, so consistent estimators of `(α, β, θ)` give a consistent standardized
comparison.

The integrals are controlled by a **local envelope** (`LocalEnvelope`): near every `(c, β)` the
integrands `|g⁻¹(c + xᵀβ)|` are bounded by one integrable function. A bounded inverse link (for
example the logistic function) has a local envelope under every finite law
(`localEnvelope_of_bounded`).

## Main definitions

* `LocalEnvelope F ginv`.

## Main results

* `continuousAt_shiftMean_joint`: the shift mean `∫ g⁻¹(c + xᵀβ) dF` is jointly continuous in
  `(c, β)`.
* `continuousAt_calibratedShift`: the calibrated shift is jointly continuous at every attained
  `(β₀, θ₀)`.
* `tendstoInMeasure_unanchored_standardized`: consistency of the standardized comparison;
  `tendstoInMeasure_unanchored_marginalEffect`: its limit is the causal marginal effect under the
  assumptions of the unanchored identification theorem.

## References

* D. M. Phillippo, A. E. Ades, S. Dias, S. Palmer, K. R. Abrams and N. J. Welton, *Methods for
  population-adjusted indirect comparisons in health technology appraisal*, Medical Decision
  Making 38 (2018).
* D. M. Phillippo, S. Dias, A. E. Ades, M. Belger, A. Brnabic, A. Schacht, D. Saure, Z. Kadziola
  and N. J. Welton, *Multilevel network meta-regression for population-adjusted treatment
  comparisons*, Journal of the Royal Statistical Society Series A 183 (2020).
-/

@[expose] public section

namespace CausalInference

namespace NetworkMetaRegression

open MeasureTheory Filter Topology EffectMeasure

variable {p : ℕ}

/-! ### Local envelopes and continuity -/

/-- A **local envelope** of the integrands `g⁻¹(c + xᵀβ)` under `F`: near every `(c₀, β₀)` they
are bounded by one `F`-integrable function. -/
def LocalEnvelope (F : Measure (Fin p → ℝ)) (ginv : ℝ → ℝ) : Prop :=
  ∀ (c₀ : ℝ) (β₀ : Fin p → ℝ), ∃ H : (Fin p → ℝ) → ℝ, Integrable H F ∧
    ∀ᶠ q in 𝓝 (c₀, β₀), ∀ x, |ginv (q.1 + x ⬝ᵥ q.2)| ≤ H x

/-- A bounded inverse link has a local envelope under every finite law. -/
theorem localEnvelope_of_bounded {F : Measure (Fin p → ℝ)} [IsFiniteMeasure F] {ginv : ℝ → ℝ}
    {B : ℝ} (hB : ∀ s, |ginv s| ≤ B) : LocalEnvelope F ginv :=
  fun _ _ => ⟨fun _ => B, integrable_const B, Eventually.of_forall fun _ _ => hB _⟩

variable {F : Measure (Fin p → ℝ)} {ginv : ℝ → ℝ}

/-- The integrand `x ↦ g⁻¹(c + xᵀβ)` of a continuous `g⁻¹` is continuous. -/
theorem continuous_inv_link_affine (hcont : Continuous ginv) (c : ℝ) (β : Fin p → ℝ) :
    Continuous fun x : Fin p → ℝ => ginv (c + x ⬝ᵥ β) := by
  unfold dotProduct
  fun_prop

/-- Under a local envelope every integrand `g⁻¹(c + xᵀβ)` of a continuous `g⁻¹` is integrable. -/
theorem LocalEnvelope.integrable (hcont : Continuous ginv) (hE : LocalEnvelope F ginv) (c : ℝ)
    (β : Fin p → ℝ) : Integrable (fun x => ginv (c + x ⬝ᵥ β)) F := by
  obtain ⟨H, hH, hev⟩ := hE c β
  exact hH.mono' (continuous_inv_link_affine hcont c β).aestronglyMeasurable
    (ae_of_all _ fun x => by simpa [Real.norm_eq_abs] using hev.self_of_nhds x)

/-- **Joint continuity of the shift mean** `(c, β) ↦ ∫ g⁻¹(c + xᵀβ) dF` for a continuous `g⁻¹`
with a local envelope. -/
theorem continuousAt_shiftMean_joint (hcont : Continuous ginv) (hE : LocalEnvelope F ginv)
    (q₀ : ℝ × (Fin p → ℝ)) :
    ContinuousAt (fun q : ℝ × (Fin p → ℝ) => shiftMean F ginv (fun x => x ⬝ᵥ q.2) q.1) q₀ := by
  obtain ⟨H, hH, hev⟩ := hE q₀.1 q₀.2
  refine continuousAt_of_dominated (bound := H)
    (Eventually.of_forall fun q => (continuous_inv_link_affine hcont q.1 q.2).aestronglyMeasurable)
    (hev.mono fun q hq => ae_of_all _ fun x => by simpa [Real.norm_eq_abs] using hq x) hH
    (ae_of_all _ fun x => ?_)
  have : Continuous fun q : ℝ × (Fin p → ℝ) => ginv (q.1 + x ⬝ᵥ q.2) := by
    unfold dotProduct
    fun_prop
  exact this.continuousAt

/-- **The calibrated shift is jointly continuous at every attained mean.** For a continuous,
strictly increasing `g⁻¹` with a local envelope under the probability law `F`, the map
`(β, θ) ↦ c(β, θ)` is continuous at `(β₀, ∫ g⁻¹(c₀ + xᵀβ₀) dF)`. Near that point the calibration
equation has a root within `ε` of `c₀`, by the intermediate value theorem. -/
theorem continuousAt_calibratedShift [IsProbabilityMeasure F] (hmono : StrictMono ginv)
    (hcont : Continuous ginv) (hE : LocalEnvelope F ginv) (β₀ : Fin p → ℝ) (c₀ : ℝ) :
    ContinuousAt (fun q : (Fin p → ℝ) × ℝ => calibratedShift F ginv q.1 q.2)
      (β₀, shiftMean F ginv (fun x => x ⬝ᵥ β₀) c₀) := by
  have hint : ∀ β c, Integrable (fun x => ginv (c + x ⬝ᵥ β)) F := fun β c =>
    hE.integrable hcont c β
  rw [ContinuousAt, calibratedShift_eq hmono (hint β₀), Metric.tendsto_nhds]
  intro ε hε
  set θ₀ := shiftMean F ginv (fun x => x ⬝ᵥ β₀) c₀
  have hsm := shiftMean_strictMono hmono (hint β₀)
  have hlo : shiftMean F ginv (fun x => x ⬝ᵥ β₀) (c₀ - ε / 2) - θ₀ < 0 :=
    sub_neg.2 (hsm (by linarith))
  have hhi : 0 < shiftMean F ginv (fun x => x ⬝ᵥ β₀) (c₀ + ε / 2) - θ₀ :=
    sub_pos.2 (hsm (by linarith))
  have hc : ∀ d : ℝ, ContinuousAt
      (fun q : (Fin p → ℝ) × ℝ => shiftMean F ginv (fun x => x ⬝ᵥ q.1) d - q.2) (β₀, θ₀) :=
    fun d => by
      have h1 : ContinuousAt
          (fun q : (Fin p → ℝ) × ℝ => shiftMean F ginv (fun x => x ⬝ᵥ q.1) d) (β₀, θ₀) :=
        (continuousAt_shiftMean_joint hcont hE (d, β₀)).comp (x := (β₀, θ₀))
          (f := fun q : (Fin p → ℝ) × ℝ => (d, q.1)) (by fun_prop)
      exact h1.sub continuousAt_snd
  filter_upwards [(hc _).eventually (gt_mem_nhds hlo), (hc _).eventually (lt_mem_nhds hhi)]
    with q hq1 hq2
  have hcq : Continuous fun c => shiftMean F ginv (fun x => x ⬝ᵥ q.1) c :=
    continuous_iff_continuousAt.2 fun c =>
      (continuousAt_shiftMean_joint hcont hE (c, q.1)).comp
        (f := fun c : ℝ => (c, q.1)) (by fun_prop)
  obtain ⟨c, hcI, hcval⟩ := intermediate_value_Ioo (by linarith) hcq.continuousOn
    (⟨by linarith, by linarith⟩ :
      q.2 ∈ Set.Ioo (shiftMean F ginv (fun x => x ⬝ᵥ q.1) (c₀ - ε / 2))
        (shiftMean F ginv (fun x => x ⬝ᵥ q.1) (c₀ + ε / 2)))
  have : calibratedShift F ginv q.1 q.2 = c := hcval ▸ calibratedShift_eq hmono (hint q.1)
  rw [this, Real.dist_eq, abs_lt]
  constructor <;> linarith [hcI.1, hcI.2]

/-! ### Consistency -/

section Consistency

variable {Ω J K : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- **Consistency of the unanchored standardized comparison.** Let `g⁻¹` be continuous and
strictly increasing with local envelopes under the probability law `F_B` of the aggregate study
and the target covariate law `Q`, let `a` and `b` share their effect modifiers in `M`, and let
`g` be continuous at the target means `∫ m_A dQ`, `∫ m_B dQ` of the surfaces of `a` (baseline
`μ_{j_A}`) and `b` (baseline `μ_{j_B}`). If `αhat`, `βhat`, `θhat` converge in probability to
the cell intercept and cell slope of `a` and the aggregate mean of `b` in `j_B`, the standardized
comparison `g(∫ g⁻¹(c(βhat, θhat) + xᵀβhat) dQ) - g(∫ g⁻¹(αhat + xᵀβhat) dQ)` converges in
probability to the
target estimand `g(∫ m_B dQ) - g(∫ m_A dQ)`. -/
theorem tendstoInMeasure_unanchored_standardized {FB Q : Measure (Fin p → ℝ)}
    [IsProbabilityMeasure FB] (hmono : StrictMono ginv) (hcont : Continuous ginv)
    (hEB : LocalEnvelope FB ginv) (hEQ : LocalEnvelope Q ginv) {g : ℝ → ℝ}
    {M : MultilevelModel J K p} {jA jB : J} {a b : K} (hM : M.SharedEffectModifiers {a, b})
    (hgA : ContinuousAt g (∫ x, M.surface ginv (M.μ jA) a x ∂Q))
    (hgB : ContinuousAt g (∫ x, M.surface ginv (M.μ jB) b x ∂Q))
    {αhat θhat : ℕ → Ω → ℝ} {βhat : ℕ → Ω → Fin p → ℝ}
    (hα : TendstoInMeasure P αhat atTop (fun _ => M.cellIntercept jA a))
    (hβ : TendstoInMeasure P βhat atTop (fun _ => M.cellSlope a))
    (hθ : TendstoInMeasure P θhat atTop (fun _ => M.armMean ginv (M.μ jB) FB b)) :
    TendstoInMeasure P
      (fun n ω => g (shiftMean Q ginv (fun x => x ⬝ᵥ βhat n ω)
          (calibratedShift FB ginv (βhat n ω) (θhat n ω))) -
        g (shiftMean Q ginv (fun x => x ⬝ᵥ βhat n ω) (αhat n ω))) atTop
      (fun _ => linkMarginal g Q (M.surface ginv (M.μ jA) a) (M.surface ginv (M.μ jB) b)) := by
  have hs := (M.sharedEffectModifiers_pair_iff_cellSlope a b).1 hM
  have hclass : M ∈ MultilevelModel.unanchoredClass ginv FB a b :=
    ⟨hM, fun s => hEB.integrable hcont s _⟩
  obtain ⟨hcB, hval⟩ :=
    MultilevelModel.unanchored_estimand_eq_calibrated (jA := jA) hmono hclass Q g
  have hθ₀ : M.armMean ginv (M.μ jB) FB b =
      shiftMean FB ginv (fun x => x ⬝ᵥ M.cellSlope a) (M.cellIntercept jB b) := by
    rw [MultilevelModel.armMean_eq_cell, hs]
  have hmA : ∫ x, M.surface ginv (M.μ jA) a x ∂Q =
      shiftMean Q ginv (fun x => x ⬝ᵥ M.cellSlope a) (M.cellIntercept jA a) := by
    rw [MultilevelModel.surface_eq_cell]; rfl
  have hmB : ∫ x, M.surface ginv (M.μ jB) b x ∂Q =
      shiftMean Q ginv (fun x => x ⬝ᵥ M.cellSlope a) (M.cellIntercept jB b) := by
    rw [MultilevelModel.surface_eq_cell, hs]; rfl
  set Φ : ℝ × (Fin p → ℝ) × ℝ → ℝ := fun q =>
    g (shiftMean Q ginv (fun x => x ⬝ᵥ q.2.1) (calibratedShift FB ginv q.2.1 q.2.2)) -
      g (shiftMean Q ginv (fun x => x ⬝ᵥ q.2.1) q.1) with hΦ
  have hcal : ContinuousAt (fun q : ℝ × (Fin p → ℝ) × ℝ => calibratedShift FB ginv q.2.1 q.2.2)
      (M.cellIntercept jA a, M.cellSlope a, M.armMean ginv (M.μ jB) FB b) := by
    have h1 := continuousAt_calibratedShift hmono hcont hEB (M.cellSlope a) (M.cellIntercept jB b)
    rw [← hθ₀] at h1
    exact h1.comp (x := (M.cellIntercept jA a, M.cellSlope a, M.armMean ginv (M.μ jB) FB b))
      (f := fun q : ℝ × (Fin p → ℝ) × ℝ => (q.2.1, q.2.2)) (by fun_prop)
  have hcal0 : calibratedShift FB ginv (M.cellSlope a) (M.armMean ginv (M.μ jB) FB b) =
      M.cellIntercept jB b := hcB.symm
  have hB : ContinuousAt (fun q : ℝ × (Fin p → ℝ) × ℝ =>
      g (shiftMean Q ginv (fun x => x ⬝ᵥ q.2.1) (calibratedShift FB ginv q.2.1 q.2.2)))
      (M.cellIntercept jA a, M.cellSlope a, M.armMean ginv (M.μ jB) FB b) := by
    refine ContinuousAt.comp (g := g) ?_ ?_
    · simp only [hcal0]
      rw [← hmB]
      exact hgB
    · have h1 := continuousAt_shiftMean_joint hcont hEQ (M.cellIntercept jB b, M.cellSlope a)
      rw [← hcal0] at h1
      exact h1.comp (f := fun q : ℝ × (Fin p → ℝ) × ℝ =>
        (calibratedShift FB ginv q.2.1 q.2.2, q.2.1)) (hcal.prodMk continuousAt_snd.fst)
  have hA : ContinuousAt (fun q : ℝ × (Fin p → ℝ) × ℝ =>
      g (shiftMean Q ginv (fun x => x ⬝ᵥ q.2.1) q.1))
      (M.cellIntercept jA a, M.cellSlope a, M.armMean ginv (M.μ jB) FB b) := by
    refine ContinuousAt.comp (g := g) ?_ ?_
    · rw [← hmA]; exact hgA
    · exact (continuousAt_shiftMean_joint hcont hEQ _).comp
        (f := fun q : ℝ × (Fin p → ℝ) × ℝ => (q.1, q.2.1)) (by fun_prop)
  have hconv := (hα.prodMk (hβ.prodMk hθ)).comp_continuousAt (hB.sub hA)
  have hlim : Φ (M.cellIntercept jA a, M.cellSlope a, M.armMean ginv (M.μ jB) FB b) =
      linkMarginal g Q (M.surface ginv (M.μ jA) a) (M.surface ginv (M.μ jB) b) := by
    rw [hval]
    rfl
  rw [← hlim]
  exact hconv

/-- **Consistency for the causal estimand.** In an unanchored setting `S` (sources of `a` and
`b`, target) with finite measures, let the model surfaces of `a` at `μ_{j_A}` and `b` at
`μ_{j_B}` satisfy the assumptions of the unanchored identification theorem
(`UnanchoredSetting.IdentificationAssumptions`: conditional mean functions in the sources,
absolute constancy and overlap with the target). Under the hypotheses of
`tendstoInMeasure_unanchored_standardized` with `Q` the target covariate law, the standardized
comparison converges in probability to the marginal effect `g(E Y(b)) - g(E Y(a))` in the
target. -/
theorem tendstoInMeasure_unanchored_marginalEffect {Ω₁ Ω₂ Ω₃ : Type*} [MeasurableSpace Ω₁]
    [MeasurableSpace Ω₂] [MeasurableSpace Ω₃]
    {S : IndirectComparison.UnanchoredSetting Ω₁ Ω₂ Ω₃ (Fin p → ℝ) K}
    [IsFiniteMeasure S.sourceA.μ] [IsFiniteMeasure S.sourceB.μ] [IsFiniteMeasure S.target.μ]
    {FB : Measure (Fin p → ℝ)} [IsProbabilityMeasure FB] (hmono : StrictMono ginv)
    (hcont : Continuous ginv) (hEB : LocalEnvelope FB ginv)
    (hEQ : LocalEnvelope S.target.covLaw ginv) {g : ℝ → ℝ} {D : Set ℝ}
    {M : MultilevelModel J K p} {jA jB : J}
    (hS : S.IdentificationAssumptions D (M.surface ginv (M.μ jA) S.a)
      (M.surface ginv (M.μ jB) S.b))
    (hM : M.SharedEffectModifiers {S.a, S.b})
    (hgA : ContinuousAt g (∫ x, M.surface ginv (M.μ jA) S.a x ∂S.target.covLaw))
    (hgB : ContinuousAt g (∫ x, M.surface ginv (M.μ jB) S.b x ∂S.target.covLaw))
    {αhat θhat : ℕ → Ω → ℝ} {βhat : ℕ → Ω → Fin p → ℝ}
    (hα : TendstoInMeasure P αhat atTop (fun _ => M.cellIntercept jA S.a))
    (hβ : TendstoInMeasure P βhat atTop (fun _ => M.cellSlope S.a))
    (hθ : TendstoInMeasure P θhat atTop (fun _ => M.armMean ginv (M.μ jB) FB S.b)) :
    TendstoInMeasure P
      (fun n ω => g (shiftMean S.target.covLaw ginv (fun x => x ⬝ᵥ βhat n ω)
          (calibratedShift FB ginv (βhat n ω) (θhat n ω))) -
        g (shiftMean S.target.covLaw ginv (fun x => x ⬝ᵥ βhat n ω) (αhat n ω))) atTop
      (fun _ => S.target.marginalEffect g S.a S.b) := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, he⟩ := hS.identification g
  rw [he]
  exact tendstoInMeasure_unanchored_standardized hmono hcont hEB hEQ hM hgA hgB hα hβ hθ

end Consistency

/-- **Instance of the consistency theorem.** The logistic inverse link `Real.sigmoid` (bounded
by `1`), `F_B = Q = binaryLaw (1/2)`, the scale `g = id`, the model with study intercepts
`μ_{j_A} = 0`, `μ_{j_B} = 1` and all other parameters `0`, and the exact estimators equal to the
true values. The comparison converges to `σ(1) - σ(0) = σ(1) - 1/2`. -/
theorem tendstoInMeasure_unanchored_standardized_instance {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) :
    let M : MultilevelModel Bool Bool 1 := ⟨fun j => if j then 0 else 1, 0, 0, 0⟩
    TendstoInMeasure P
      (fun (_ : ℕ) (_ : Ω) => shiftMean (binaryLaw (1 / 2)) Real.sigmoid
          (fun x => x ⬝ᵥ M.cellSlope true)
          (calibratedShift (binaryLaw (1 / 2)) Real.sigmoid (M.cellSlope true)
            (M.armMean Real.sigmoid (M.μ false) (binaryLaw (1 / 2)) false)) -
        shiftMean (binaryLaw (1 / 2)) Real.sigmoid (fun x => x ⬝ᵥ M.cellSlope true)
          (M.cellIntercept true true)) atTop
      (fun _ => Real.sigmoid 1 - 1 / 2) := by
  intro M
  have : IsProbabilityMeasure (binaryLaw (1 / 2)) := isProbabilityMeasure_binaryLaw_half
  have hE : LocalEnvelope (binaryLaw (1 / 2)) Real.sigmoid := localEnvelope_of_bounded (B := 1)
    fun s => by rw [abs_of_pos (Real.sigmoid_pos s)]; exact (Real.sigmoid_lt_one s).le
  have h := tendstoInMeasure_unanchored_standardized (P := P) (g := id) (M := M) (jA := true)
    (jB := false) (a := true) (b := false) Real.sigmoid_strictMono continuous_sigmoid hE hE
    (by rw [MultilevelModel.sharedEffectModifiers_iff]; intro _ _ _ _; rfl)
    continuousAt_id continuousAt_id (tendstoInMeasure_const _) (tendstoInMeasure_const _)
    (tendstoInMeasure_const _)
  have hv : linkMarginal id (binaryLaw (1 / 2)) (M.surface Real.sigmoid (M.μ true) true)
      (M.surface Real.sigmoid (M.μ false) false) = Real.sigmoid 1 - 1 / 2 := by
    rw [linkMarginal, integral_binaryLaw ⟨by norm_num, by norm_num⟩,
      integral_binaryLaw ⟨by norm_num, by norm_num⟩]
    simp [M, MultilevelModel.surface, MultilevelModel.eta,
      NetworkMetaAnalysis.metaRegressionPredictor]
    ring
  rw [hv] at h
  simpa using h

/-- The model of the consistency instances: study intercepts `0`, prognostic effects `0`,
`γ_true = 0`, `γ_false = 1` and no effect modification. -/
noncomputable def consistencyModel : MultilevelModel Bool Bool 1 :=
  ⟨fun _ => 0, 0, fun t => if t then 0 else 1, 0⟩

/-- The population under `binaryLaw (1/2)` with covariate the identity and potential outcomes the
logistic surfaces of `consistencyModel` at baseline `0`. -/
noncomputable def consistencyPopulation : IndirectComparison.Population (Fin 1 → ℝ) (Fin 1 → ℝ)
    Bool :=
  ⟨binaryLaw (1 / 2), id, fun t => consistencyModel.surface Real.sigmoid 0 t⟩

/-- The unanchored setting with both sources and the target equal to `consistencyPopulation`,
`a = true` and `b = false`. -/
noncomputable def consistencySetting :
    IndirectComparison.UnanchoredSetting (Fin 1 → ℝ) (Fin 1 → ℝ) (Fin 1 → ℝ) (Fin 1 → ℝ) Bool :=
  ⟨consistencyPopulation, consistencyPopulation, consistencyPopulation, true, false⟩

/-- **Instance of consistency for the causal estimand** in `consistencySetting` with the logistic
inverse link, `F_B = binaryLaw (1/2)`, the scale `g = id`, `D = Set.univ` and the exact
estimators. All assumptions of the unanchored identification theorem hold, since sources and
target coincide and the outcomes are the model surfaces. -/
theorem tendstoInMeasure_unanchored_marginalEffect_instance {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) :
    TendstoInMeasure P
      (fun (_ : ℕ) (_ : Ω) =>
        shiftMean consistencySetting.target.covLaw Real.sigmoid
            (fun x => x ⬝ᵥ consistencyModel.cellSlope true)
            (calibratedShift (binaryLaw (1 / 2)) Real.sigmoid (consistencyModel.cellSlope true)
              (consistencyModel.armMean Real.sigmoid (consistencyModel.μ false)
                (binaryLaw (1 / 2)) false)) -
          shiftMean consistencySetting.target.covLaw Real.sigmoid
            (fun x => x ⬝ᵥ consistencyModel.cellSlope true)
            (consistencyModel.cellIntercept true true)) atTop
      (fun _ => consistencySetting.target.marginalEffect id true false) := by
  have : IsProbabilityMeasure (binaryLaw (1 / 2)) := isProbabilityMeasure_binaryLaw_half
  have hcov : consistencyPopulation.covLaw = binaryLaw (1 / 2) := by
    simp [IndirectComparison.Population.covLaw, consistencyPopulation]
  have : IsFiniteMeasure consistencyPopulation.μ := by
    simp only [consistencyPopulation]; infer_instance
  have hE : LocalEnvelope (binaryLaw (1 / 2)) Real.sigmoid := localEnvelope_of_bounded (B := 1)
    fun s => by rw [abs_of_pos (Real.sigmoid_pos s)]; exact (Real.sigmoid_lt_one s).le
  have hc : ∀ t, consistencyPopulation.IsCondMean t (consistencyModel.surface Real.sigmoid 0 t) :=
    fun t => IndirectComparison.Population.isCondMean_of_eq_comp measurable_id
      (consistencyModel.measurable_surface Real.sigmoid_strictMono.monotone.measurable 0 t) rfl
      (integrable_binaryLaw _ _)
  have hsi : ∀ t, Transport.StructurallyInvariant consistencyPopulation.μ consistencyPopulation.X
      (consistencyPopulation.Y t) consistencyPopulation.μ consistencyPopulation.X
      (consistencyPopulation.Y t) := fun t => by
    refine ⟨consistencyModel.surface Real.sigmoid 0 t, ?_⟩
    rw [IndirectComparison.Population.isCommonRegression_iff]
    exact ⟨hc t, hc t⟩
  have hS : consistencySetting.IdentificationAssumptions Set.univ
      (consistencyModel.surface Real.sigmoid (consistencyModel.μ true) consistencySetting.a)
      (consistencyModel.surface Real.sigmoid (consistencyModel.μ false) consistencySetting.b) :=
    { measurable_sourceA := measurable_id
      measurable_sourceB := measurable_id
      measurable_target := measurable_id
      integrable_sourceA := integrable_binaryLaw _ _
      integrable_sourceB := integrable_binaryLaw _ _
      integrable_target_a := integrable_binaryLaw _ _
      integrable_target_b := integrable_binaryLaw _ _
      mem_a := trivial
      mem_b := trivial
      isCondMean_a := hc true
      isCondMean_b := hc false
      structurallyInvariant_a := hsi true
      structurallyInvariant_b := hsi false
      overlap_a := Measure.AbsolutelyContinuous.rfl
      overlap_b := Measure.AbsolutelyContinuous.rfl
      integrable_weighted_a := integrable_binaryLaw _ _
      integrable_weighted_b := integrable_binaryLaw _ _ }
  have : IsFiniteMeasure consistencySetting.sourceA.μ := by
    simp only [consistencySetting]; infer_instance
  have : IsFiniteMeasure consistencySetting.sourceB.μ := by
    simp only [consistencySetting]; infer_instance
  have : IsFiniteMeasure consistencySetting.target.μ := by
    simp only [consistencySetting]; infer_instance
  exact tendstoInMeasure_unanchored_marginalEffect (S := consistencySetting) (jA := true)
    (jB := false) (g := id) Real.sigmoid_strictMono continuous_sigmoid hE
    (by rw [consistencySetting, hcov]; exact hE) hS
    (by rw [MultilevelModel.sharedEffectModifiers_iff]; intro _ _ _ _; rfl)
    continuousAt_id continuousAt_id (tendstoInMeasure_const _) (tendstoInMeasure_const _)
    (tendstoInMeasure_const _)

end NetworkMetaRegression

end CausalInference
