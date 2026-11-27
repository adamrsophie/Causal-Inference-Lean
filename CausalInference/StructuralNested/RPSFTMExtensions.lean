/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.StructuralNested.RPSFTMCounterexamples

/-!
# Extensions of the RPSFTM: strata, several treatment levels, a zero first stage

## Main definitions

* `SwitchingTrial.RandomizedWithin μ V`: **randomization within strata** of a baseline covariate
  `V`: for every value `v` with `P(V = v) > 0`, the arm is independent of the untreated time
  under `P( · | V = v)`. This is the per-stratum form, suited to a covariate with countably many
  values; the strata are the events `V = v`.
* `SwitchingTrial.stratifiedG μ V S w ψ = Σ_{v ∈ S} w v · gMean (P( · | V = v)) ψ`: a stratified
  estimating function with weights `w`.
* `StructuralNested.MultiLevelTrial`: a trial in which observed time is split into times
  `T_k` at treatment levels `k ∈ ι`, with untreated time `Σ_k exp (ψ_k) T_k`
  (`MultiLevelTrial.counterfactual`).

## Main results

* Baseline covariate adjustment (TSD 16, Section 3.2.2: "it is possible to adjust for baseline
  covariates within an RPSFTM analysis"):
  `SwitchingTrial.stratum_gMean_eq_zero_iff`, `SwitchingTrial.stratum_armLaw_eq`,
  `SwitchingTrial.stratum_eq_trueParam_of_armLaw_eq`: identification within each stratum;
  `SwitchingTrial.stratifiedG_eq`: the stratified estimating function is
  `(exp ψ - exp ψ₀) Σ_v w v (first stage in stratum v)`; `SwitchingTrial.stratifiedG_trueParam`,
  `SwitchingTrial.stratifiedG_eq_zero_iff`, `SwitchingTrial.stratifiedG_eq_zero_iff_of_sign`:
  it vanishes at the truth, and `ψ₀` is its unique root when the weighted first stages do not
  cancel, in particular when they have one sign and one is nonzero with positive weight.
* `StrataExample`: randomization only within strata of a prognostic `V` (arm probability `3/4`
  in the good stratum and `1/4` in the poor one). Marginal randomization fails
  (`StrataExample.not_randomized`); the unstratified root has time ratio `5/14`
  (`StrataExample.unstratified_root`), the stratified estimating function has the true time ratio
  `1/2` as unique root (`StrataExample.stratified_root`).
* Several treatment levels (TSD 24, Section 4.2.1.1, the stratified RPSFTM of Xu et al.):
  `MultiLevelTrial.ofSwitching_counterfactual` (the one-parameter model is the case of two levels
  with `ψ_off = 0`), `MultiLevelTrial.meanContrast_trueParam` (the true parameter vector satisfies
  the mean randomization restriction), `MultiLevelTrial.meanContrast_eq` (the restriction is the
  single linear equation `Σ_k exp (ψ_k) (E[T_k | R = 1] - E[T_k | R = 0]) = 0` in the
  `exp (ψ_k)`), `MultiLevelTrial.not_identified` (so two free parameters are never identified by
  the mean restriction: another parameter vector, equal to `ψ₀` off two chosen levels, satisfies
  it too), and `MultiLevelTrial.twoParam_counterfactual`, the link to
  `RPSFTMCounterexample.TwoParam`.
* `ZeroFirstStage.not_identified`: two trials with the same observed data `(R, T, T^e)` (hence the
  same joint law), both randomized and with a common effect, with parameters `0` and `log (1/2)`;
  the first stage is zero.

## What TSD 24 prints about several levels

TSD 24, Section 4.2.1.1 prints no formula for the model of Xu et al. It says that the model
"reflects the RPSFTM as described in equation (1), with the difference being that a series of
parameters ψk, k=0,...., K are estimated, which represent the different 'levels' of treatment";
it mentions "potential difficulties in obtaining a unique solution", and concludes that "in
practice it is not possible to reliably estimate multiple parameters using the RPSFTM method
without making additional assumptions". `MultiLevelTrial.counterfactual` is the natural reading
of that sentence; `MultiLevelTrial.not_identified` proves the non-identification for the mean
restriction from one binary randomization.

## Sources

N. R. Latimer, K. R. Abrams, *NICE DSU Technical Support Document 16* (2014), Section 3.2.2;
H. Bell Gorrod, N. R. Latimer, K. R. Abrams, *NICE DSU Technical Support Document 24* (2024),
Section 4.2.1.1.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set

namespace CausalInference

namespace StructuralNested

/-! ### Baseline covariate adjustment -/

namespace SwitchingTrial

variable {Ω β : Type*} [MeasurableSpace Ω] {M : SwitchingTrial Ω} {μ : Measure Ω}

variable (M μ) in
/-- **Randomization within strata** of a baseline covariate `V`: for every `v` with
`P(V = v) > 0`, the arm is independent of the untreated time under `P( · | V = v)`. -/
def RandomizedWithin (V : Ω → β) : Prop :=
  ∀ v, μ (V ⁻¹' {v}) ≠ 0 → M.Randomized μ[|V ⁻¹' {v}]

/-- A stratum in which an arm has positive conditional probability has positive probability. -/
theorem stratum_ne_zero {V : Ω → β} {v : β} {r : Bool} (h : μ[|V ⁻¹' {v}] (M.arm r) ≠ 0) :
    μ (V ⁻¹' {v}) ≠ 0 := by
  intro h0
  exact h (by simp [ProbabilityTheory.cond, Measure.restrict_eq_zero.2 h0])

/-- Under a common effect, randomization, integrable `T`, `T^e` and arms of positive probability,
for any finite measure, `gMean ψ = (exp ψ - exp ψ₀) · (E[T^e | R = 1] - E[T^e | R = 0])`. -/
theorem gMean_eq_mul {ν : Measure Ω} [IsFiniteMeasure ν] (hR : Measurable M.R) {ψ₀ : ℝ}
    (h : M.CommonEffect ψ₀) (hrand : M.Randomized ν) (hT : Integrable M.T ν)
    (hTe : Integrable M.Te ν) (h1 : ν (M.arm true) ≠ 0) (h0 : ν (M.arm false) ≠ 0) (ψ : ℝ) :
    M.gMean ν ψ = (Real.exp ψ - Real.exp ψ₀) * M.meanContrast ν M.Te := by
  have t := gMean_trueParam hR h hrand hT hTe h1 h0
  rw [gMean_eq hT hTe h1 h0] at t
  rw [gMean_eq hT hTe h1 h0]
  linear_combination t

/-- **Identification within a stratum.** Under a common effect `ψ₀`, randomization within strata
of `V`, integrable `T` and `T^e`, both arms of positive probability in the stratum `V = v` and a
nonzero first stage there, `ψ₀` is the unique root of the stratum's mean-form estimating
function. -/
theorem stratum_gMean_eq_zero_iff [IsFiniteMeasure μ] (hR : Measurable M.R) {V : Ω → β}
    {ψ₀ : ℝ} (h : M.CommonEffect ψ₀) (hrand : M.RandomizedWithin μ V)
    (hT : Integrable M.T μ) (hTe : Integrable M.Te μ) {v : β}
    (h1 : μ[|V ⁻¹' {v}] (M.arm true) ≠ 0) (h0 : μ[|V ⁻¹' {v}] (M.arm false) ≠ 0)
    (hrel : M.meanContrast μ[|V ⁻¹' {v}] M.Te ≠ 0) (ψ : ℝ) :
    M.gMean μ[|V ⁻¹' {v}] ψ = 0 ↔ ψ = ψ₀ := by
  have hv := stratum_ne_zero h1
  have := cond_isProbabilityMeasure (μ := μ) hv
  exact gMean_eq_zero_iff hR h (hrand v hv) (Mediation.integrable_cond_of_integrable hT hv)
    (Mediation.integrable_cond_of_integrable hTe hv) h1 h0 hrel ψ

/-- **Equal arm laws within a stratum at the true parameter.** -/
theorem stratum_armLaw_eq [IsFiniteMeasure μ] (hR : Measurable M.R) (hTm : Measurable M.T)
    (hTem : Measurable M.Te) {V : Ω → β} {ψ₀ : ℝ} (h : M.CommonEffect ψ₀)
    (hrand : M.RandomizedWithin μ V) {v : β} (h1 : μ[|V ⁻¹' {v}] (M.arm true) ≠ 0)
    (h0 : μ[|V ⁻¹' {v}] (M.arm false) ≠ 0) :
    M.armLaw μ[|V ⁻¹' {v}] (M.counterfactual ψ₀) true =
      M.armLaw μ[|V ⁻¹' {v}] (M.counterfactual ψ₀) false := by
  have hv := stratum_ne_zero h1
  have := cond_isProbabilityMeasure (μ := μ) hv
  exact armLaw_counterfactual_trueParam hR hTm hTem h (hrand v hv) h1 h0

/-- **Uniqueness of the distributional root within a stratum** under a nonzero first stage in
the stratum. -/
theorem stratum_eq_trueParam_of_armLaw_eq [IsFiniteMeasure μ] (hR : Measurable M.R)
    (hTm : Measurable M.T) (hTem : Measurable M.Te) {V : Ω → β} {ψ₀ : ℝ}
    (h : M.CommonEffect ψ₀) (hrand : M.RandomizedWithin μ V) (hT : Integrable M.T μ)
    (hTe : Integrable M.Te μ) {v : β} (h1 : μ[|V ⁻¹' {v}] (M.arm true) ≠ 0)
    (h0 : μ[|V ⁻¹' {v}] (M.arm false) ≠ 0) (hrel : M.meanContrast μ[|V ⁻¹' {v}] M.Te ≠ 0)
    {ψ : ℝ} (hlaw : M.armLaw μ[|V ⁻¹' {v}] (M.counterfactual ψ) true =
      M.armLaw μ[|V ⁻¹' {v}] (M.counterfactual ψ) false) : ψ = ψ₀ := by
  have hv := stratum_ne_zero h1
  have := cond_isProbabilityMeasure (μ := μ) hv
  exact eq_trueParam_of_armLaw_eq hR hTm hTem h (hrand v hv)
    (Mediation.integrable_cond_of_integrable hT hv)
    (Mediation.integrable_cond_of_integrable hTe hv) h1 h0 hrel hlaw

variable (M μ) in
/-- **The stratified estimating function**: the weighted sum over the strata `v ∈ S` of the
mean-form estimating functions within strata, `Σ_{v ∈ S} w v · gMean (P( · | V = v)) ψ`. -/
noncomputable def stratifiedG (V : Ω → β) (S : Finset β) (w : β → ℝ) (ψ : ℝ) : ℝ :=
  ∑ v ∈ S, w v * M.gMean μ[|V ⁻¹' {v}] ψ

/-- Under the hypotheses of `stratum_gMean_eq_zero_iff` for every stratum in `S` (without the
first stage condition), `stratifiedG ψ = (exp ψ - exp ψ₀) Σ_{v ∈ S} w v · (first stage in v)`. -/
theorem stratifiedG_eq [IsFiniteMeasure μ] (hR : Measurable M.R) {V : Ω → β} {ψ₀ : ℝ}
    (h : M.CommonEffect ψ₀) (hrand : M.RandomizedWithin μ V) (hT : Integrable M.T μ)
    (hTe : Integrable M.Te μ) {S : Finset β}
    (h1 : ∀ v ∈ S, μ[|V ⁻¹' {v}] (M.arm true) ≠ 0)
    (h0 : ∀ v ∈ S, μ[|V ⁻¹' {v}] (M.arm false) ≠ 0) (w : β → ℝ) (ψ : ℝ) :
    M.stratifiedG μ V S w ψ = (Real.exp ψ - Real.exp ψ₀) *
      ∑ v ∈ S, w v * M.meanContrast μ[|V ⁻¹' {v}] M.Te := by
  rw [stratifiedG, Finset.mul_sum]
  refine Finset.sum_congr rfl fun v hvS ↦ ?_
  have hv := stratum_ne_zero (h1 v hvS)
  have := cond_isProbabilityMeasure (μ := μ) hv
  rw [gMean_eq_mul hR h (hrand v hv) (Mediation.integrable_cond_of_integrable hT hv)
    (Mediation.integrable_cond_of_integrable hTe hv) (h1 v hvS) (h0 v hvS) ψ]
  ring

/-- **The stratified estimating function vanishes at the true parameter.** -/
theorem stratifiedG_trueParam [IsFiniteMeasure μ] (hR : Measurable M.R) {V : Ω → β} {ψ₀ : ℝ}
    (h : M.CommonEffect ψ₀) (hrand : M.RandomizedWithin μ V) (hT : Integrable M.T μ)
    (hTe : Integrable M.Te μ) {S : Finset β}
    (h1 : ∀ v ∈ S, μ[|V ⁻¹' {v}] (M.arm true) ≠ 0)
    (h0 : ∀ v ∈ S, μ[|V ⁻¹' {v}] (M.arm false) ≠ 0) (w : β → ℝ) :
    M.stratifiedG μ V S w ψ₀ = 0 := by
  rw [stratifiedG_eq hR h hrand hT hTe h1 h0, sub_self, zero_mul]

/-- **Identification by the stratified estimating function.** If the weighted first stages do
not cancel, `Σ_{v ∈ S} w v (E[T^e | R = 1, V = v] - E[T^e | R = 0, V = v]) ≠ 0`, then `ψ₀` is the
unique root of `stratifiedG`. -/
theorem stratifiedG_eq_zero_iff [IsFiniteMeasure μ] (hR : Measurable M.R) {V : Ω → β}
    {ψ₀ : ℝ} (h : M.CommonEffect ψ₀) (hrand : M.RandomizedWithin μ V) (hT : Integrable M.T μ)
    (hTe : Integrable M.Te μ) {S : Finset β}
    (h1 : ∀ v ∈ S, μ[|V ⁻¹' {v}] (M.arm true) ≠ 0)
    (h0 : ∀ v ∈ S, μ[|V ⁻¹' {v}] (M.arm false) ≠ 0) {w : β → ℝ}
    (hrel : ∑ v ∈ S, w v * M.meanContrast μ[|V ⁻¹' {v}] M.Te ≠ 0) (ψ : ℝ) :
    M.stratifiedG μ V S w ψ = 0 ↔ ψ = ψ₀ := by
  rw [stratifiedG_eq hR h hrand hT hTe h1 h0]
  constructor
  · intro e
    exact Real.exp_injective (sub_eq_zero.1 ((mul_eq_zero.1 e).resolve_right hrel))
  · rintro rfl; rw [sub_self, zero_mul]

/-- **Identification when the first stages have one sign.** With nonnegative weights, if
`σ · (first stage in v) ≥ 0` for every stratum of `S` (so all first stages have the sign of `σ`)
and it is positive in one stratum with positive weight, `ψ₀` is the unique root of
`stratifiedG`. -/
theorem stratifiedG_eq_zero_iff_of_sign [IsFiniteMeasure μ] (hR : Measurable M.R) {V : Ω → β}
    {ψ₀ : ℝ} (h : M.CommonEffect ψ₀) (hrand : M.RandomizedWithin μ V) (hT : Integrable M.T μ)
    (hTe : Integrable M.Te μ) {S : Finset β}
    (h1 : ∀ v ∈ S, μ[|V ⁻¹' {v}] (M.arm true) ≠ 0)
    (h0 : ∀ v ∈ S, μ[|V ⁻¹' {v}] (M.arm false) ≠ 0) {w : β → ℝ} (hw : ∀ v ∈ S, 0 ≤ w v)
    (σ : ℝ) (hs : ∀ v ∈ S, 0 ≤ σ * M.meanContrast μ[|V ⁻¹' {v}] M.Te)
    (hex : ∃ v ∈ S, 0 < w v ∧ 0 < σ * M.meanContrast μ[|V ⁻¹' {v}] M.Te) (ψ : ℝ) :
    M.stratifiedG μ V S w ψ = 0 ↔ ψ = ψ₀ := by
  refine stratifiedG_eq_zero_iff hR h hrand hT hTe h1 h0 ?_ ψ
  intro hzero
  obtain ⟨v₁, hv₁, hw₁, hs₁⟩ := hex
  have hpos : 0 < ∑ v ∈ S, w v * (σ * M.meanContrast μ[|V ⁻¹' {v}] M.Te) :=
    Finset.sum_pos' (fun v hv ↦ mul_nonneg (hw v hv) (hs v hv)) ⟨v₁, hv₁, mul_pos hw₁ hs₁⟩
  have : ∑ v ∈ S, w v * (σ * M.meanContrast μ[|V ⁻¹' {v}] M.Te) =
      σ * ∑ v ∈ S, w v * M.meanContrast μ[|V ⁻¹' {v}] M.Te := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun v _ ↦ by ring
  rw [this, hzero, mul_zero] at hpos
  exact lt_irrefl _ hpos

end SwitchingTrial

/-! ### Several treatment levels -/

/-- A two-arm trial in which the observed survival time is split into the times `Tk k` spent at
treatment levels `k ∈ ι` (one level may be "no treatment"), with the latent untreated time
`U`. -/
structure MultiLevelTrial (Ω ι : Type*) where
  /-- The randomized arm. -/
  R : Ω → Bool
  /-- The observed time at each treatment level. -/
  Tk : ι → Ω → ℝ
  /-- The latent untreated survival time. -/
  U : Ω → ℝ

namespace MultiLevelTrial

variable {Ω ι : Type*} [Fintype ι] (M : MultiLevelTrial Ω ι)

/-- **The untreated time with one parameter per level** (TSD 24, Section 4.2.1.1, reading the
model of Xu et al. as Equation (1) with a parameter `ψ_k` for each level):
`U(ψ) = Σ_k exp (ψ_k) T_k`. -/
noncomputable def counterfactual (ψ : ι → ℝ) (ω : Ω) : ℝ := ∑ k, Real.exp (ψ k) * M.Tk k ω

/-- The model holds at the parameter vector `ψ`. -/
def Model (ψ : ι → ℝ) : Prop := ∀ ω, M.U ω = M.counterfactual ψ ω

/-- The one-parameter trial as a two-level trial: level `false` is time off the experimental
treatment, level `true` time on it. -/
def ofSwitching {Ω : Type*} (M : SwitchingTrial Ω) : MultiLevelTrial Ω Bool where
  R := M.R
  Tk k := if k then M.Te else M.Tc
  U := M.U

/-- **The one-parameter model is the case of two levels with `ψ_off = 0`.** -/
theorem ofSwitching_counterfactual {Ω : Type*} (M : SwitchingTrial Ω) (ψ : ℝ) :
    (ofSwitching M).counterfactual (fun k ↦ if k then ψ else 0) = M.counterfactual ψ := by
  funext ω
  simp [counterfactual, ofSwitching, SwitchingTrial.counterfactual, add_comm]

theorem ofSwitching_model_iff {Ω : Type*} (M : SwitchingTrial Ω) (ψ : ℝ) :
    (ofSwitching M).Model (fun k ↦ if k then ψ else 0) ↔ M.CommonEffect ψ := by
  rw [Model, ofSwitching_counterfactual, M.commonEffect_iff, funext_iff]; rfl

variable [MeasurableSpace Ω] (μ : Measure Ω)

/-- The arm contrast `E[X | R = true] - E[X | R = false]`. -/
noncomputable def meanContrast (X : Ω → ℝ) : ℝ :=
  ∫ ω, X ω ∂μ[|M.R ⁻¹' {true}] - ∫ ω, X ω ∂μ[|M.R ⁻¹' {false}]

variable {M μ}

/-- **The restriction is one linear equation in the `exp (ψ_k)`.** With integrable level times
and both arms of positive probability,
`mc(U(ψ)) = Σ_k exp (ψ_k) (E[T_k | R = 1] - E[T_k | R = 0])`. -/
theorem meanContrast_eq (hT : ∀ k, Integrable (M.Tk k) μ) (h1 : μ (M.R ⁻¹' {true}) ≠ 0)
    (h0 : μ (M.R ⁻¹' {false}) ≠ 0) (ψ : ι → ℝ) :
    M.meanContrast μ (M.counterfactual ψ) =
      ∑ k, Real.exp (ψ k) * M.meanContrast μ (M.Tk k) := by
  have key : ∀ r, μ (M.R ⁻¹' {r}) ≠ 0 → ∫ ω, M.counterfactual ψ ω ∂μ[|M.R ⁻¹' {r}] =
      ∑ k, Real.exp (ψ k) * ∫ ω, M.Tk k ω ∂μ[|M.R ⁻¹' {r}] := fun r hr ↦ by
    simp only [counterfactual]
    rw [integral_finsetSum _ fun k _ ↦
      (Mediation.integrable_cond_of_integrable (hT k) hr).const_mul _]
    exact Finset.sum_congr rfl fun k _ ↦ integral_const_mul _ _
  simp only [meanContrast]
  rw [key true h1, key false h0, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun k _ ↦ by ring

/-- **The true parameter vector satisfies the randomization restriction.** Under the model at
`ψ₀`, with `U` independent of the arm, integrable `U` and both arms of positive probability, the
arm contrast of `U(ψ₀)` is zero. -/
theorem meanContrast_trueParam [IsFiniteMeasure μ] (hR : Measurable M.R) {ψ₀ : ι → ℝ}
    (h : M.Model ψ₀) (hrand : IndepFun M.R M.U μ) (hU : Integrable M.U μ)
    (h1 : μ (M.R ⁻¹' {true}) ≠ 0) (h0 : μ (M.R ⁻¹' {false}) ≠ 0) :
    M.meanContrast μ (M.counterfactual ψ₀) = 0 := by
  have hU' : M.counterfactual ψ₀ = M.U := (funext h).symm
  have e1 := Mediation.condMean_preimage_singleton_of_indepFun hrand.symm hR hU h1
  have e0 := Mediation.condMean_preimage_singleton_of_indepFun hrand.symm hR hU h0
  rw [Mediation.condMean] at e1 e0
  rw [meanContrast, hU', e1, e0, sub_self]

/-- **One linear equation does not determine two positive unknowns.** If `Σ_k c_k x⁰_k = 0` with
all `x⁰_k > 0`, then for any two distinct levels `i ≠ j` there is another positive vector
`x ≠ x⁰`, equal to `x⁰` off `{i, j}`, with `Σ_k c_k x_k = 0`. -/
theorem exists_ne_solution (c x₀ : ι → ℝ) (hx₀ : ∀ k, 0 < x₀ k)
    (h : ∑ k, c k * x₀ k = 0) {i j : ι} (hij : i ≠ j) :
    ∃ x : ι → ℝ, (∀ k, 0 < x k) ∧ ∑ k, c k * x k = 0 ∧ x ≠ x₀ ∧
      ∀ k, k ≠ i → k ≠ j → x k = x₀ k := by
  classical
  by_cases hci : c i = 0
  · refine ⟨fun k ↦ if k = i then 2 * x₀ i else x₀ k, fun k ↦ ?_, ?_, fun he ↦ ?_,
      fun k hk _ ↦ by simp only [hk, ite_false]⟩
    · by_cases hk : k = i
      · simp only [hk, ite_true]; linarith [hx₀ i]
      · simp only [hk, ite_false]; exact hx₀ k
    · rw [← h]
      refine Finset.sum_congr rfl fun k _ ↦ ?_
      by_cases hk : k = i
      · simp only [hk, ite_true, hci, zero_mul]
      · simp only [hk, ite_false]
    · have := congrFun he i
      simp only [ite_true] at this
      linarith [hx₀ i]
  · set t := min (x₀ i) (x₀ j) / (2 * (|c i| + |c j|)) with ht
    have hden : 0 < 2 * (|c i| + |c j|) := by positivity
    have htpos : 0 < t := div_pos (lt_min (hx₀ i) (hx₀ j)) hden
    have hti : t * |c j| < x₀ i := by
      have : t * (2 * (|c i| + |c j|)) = min (x₀ i) (x₀ j) := div_mul_cancel₀ _ hden.ne'
      have hm := min_le_left (x₀ i) (x₀ j)
      nlinarith [abs_nonneg (c i), abs_pos.2 hci, hx₀ i]
    have htj : t * |c i| < x₀ j := by
      have : t * (2 * (|c i| + |c j|)) = min (x₀ i) (x₀ j) := div_mul_cancel₀ _ hden.ne'
      have hm := min_le_right (x₀ i) (x₀ j)
      nlinarith [abs_nonneg (c j), abs_pos.2 hci, hx₀ j]
    let d : ι → ℝ := fun k ↦ (if k = i then t * c j else 0) - (if k = j then t * c i else 0)
    refine ⟨fun k ↦ x₀ k + d k, fun k ↦ ?_, ?_, fun he ↦ ?_, fun k hk hk' ↦ ?_⟩
    · simp only [d]
      rcases eq_or_ne k i with rfl | hk
      · simp only [ite_true, hij, ite_false, sub_zero]
        linarith [mul_le_mul_of_nonneg_left (neg_abs_le (c j)) htpos.le]
      · rcases eq_or_ne k j with rfl | hk'
        · simp only [hk, ite_true, ite_false, zero_sub]
          linarith [mul_le_mul_of_nonneg_left (le_abs_self (c i)) htpos.le]
        · simp only [hk, hk', ite_false, sub_zero, add_zero]; exact hx₀ k
    · have : ∑ k, c k * (x₀ k + d k) = ∑ k, c k * x₀ k + ∑ k, c k * d k := by
        rw [← Finset.sum_add_distrib]; exact Finset.sum_congr rfl fun k _ ↦ by ring
      rw [this, h, zero_add]
      simp only [d, mul_sub, Finset.sum_sub_distrib, mul_ite, mul_zero, Finset.sum_ite_eq',
        Finset.mem_univ, ite_true]
      ring
    · have hj := congrFun he j
      simp only [d, Ne.symm hij, ite_true, ite_false, zero_sub] at hj
      have : t * c i = 0 := by linarith
      exact hci ((mul_eq_zero.1 this).resolve_left htpos.ne')
    · simp [d, hk, hk']

/-- **Non-identification of several level parameters** (TSD 24, Section 4.2.1.1). Under the
hypotheses of `meanContrast_trueParam` and integrable level times, for any two distinct levels
`i ≠ j` there is a parameter vector `ψ ≠ ψ₀`, equal to `ψ₀` at every other level, that also
satisfies the mean randomization restriction `mc(U(ψ)) = 0`. So the restriction identifies at
most one free parameter; two or more need further assumptions. -/
theorem not_identified [IsFiniteMeasure μ] (hR : Measurable M.R)
    {ψ₀ : ι → ℝ} (h : M.Model ψ₀) (hrand : IndepFun M.R M.U μ) (hU : Integrable M.U μ)
    (hT : ∀ k, Integrable (M.Tk k) μ) (h1 : μ (M.R ⁻¹' {true}) ≠ 0)
    (h0 : μ (M.R ⁻¹' {false}) ≠ 0) {i j : ι} (hij : i ≠ j) :
    ∃ ψ : ι → ℝ, ψ ≠ ψ₀ ∧ M.meanContrast μ (M.counterfactual ψ) = 0 ∧
      ∀ k, k ≠ i → k ≠ j → ψ k = ψ₀ k := by
  have e₀ := meanContrast_trueParam hR h hrand hU h1 h0
  rw [meanContrast_eq hT h1 h0] at e₀
  obtain ⟨x, hxpos, hx, hne, hoff⟩ := exists_ne_solution (fun k ↦ M.meanContrast μ (M.Tk k))
    (fun k ↦ Real.exp (ψ₀ k)) (fun k ↦ Real.exp_pos _)
    (by rw [← e₀]; exact Finset.sum_congr rfl fun k _ ↦ mul_comm _ _) hij
  refine ⟨fun k ↦ Real.log (x k), fun he ↦ hne ?_, ?_, fun k hk hk' ↦ ?_⟩
  · funext k
    rw [← Real.exp_log (hxpos k), congrFun he k]
  · rw [meanContrast_eq hT h1 h0, ← hx]
    exact Finset.sum_congr rfl fun k _ ↦ by rw [Real.exp_log (hxpos k), mul_comm]
  · simp only [hoff k hk hk', Real.log_exp]

/-- **The link to `RPSFTMCounterexample.TwoParam`.** The untreated time of that example is the
three-level counterfactual with level times `(T^c, T₁, T₂)` and parameters `(0, ψ₁, ψ₂)`. -/
theorem twoParam_counterfactual (ψ₁ ψ₂ : ℝ) :
    RPSFTMCounterexample.TwoParam.untreated ψ₁ ψ₂ =
      (⟨fun ω ↦ ω.1, ![RPSFTMCounterexample.TwoParam.Tc, RPSFTMCounterexample.TwoParam.T₁,
        RPSFTMCounterexample.TwoParam.T₂], fun _ ↦ 0⟩ :
          MultiLevelTrial Mediation.Counterexample.Ω₀ (Fin 3)).counterfactual ![0, ψ₁, ψ₂] := by
  funext ω
  simp [RPSFTMCounterexample.TwoParam.untreated, counterfactual, Fin.sum_univ_three]

end MultiLevelTrial

/-! ### Concrete models on the eight point space -/

open Mediation.Counterexample RPSFTMCounterexample SwitchingTrial

/-- The mean of `X` under `μ₀` conditioned on an event `S`: the average of `X` over the points
of `S`. -/
theorem integral_cond_μ₀ (S : Set Ω₀) (X : Ω₀ → ℝ) :
    ∫ ω, X ω ∂μ₀[|S] =
      ((∑ ω, S.indicator (1 : Ω₀ → ℝ) ω) / 8)⁻¹ * ((∑ ω, S.indicator X ω) / 8) := by
  rw [← Mediation.condMean, Mediation.condMean_eq,
    ← integral_indicator (Set.toFinite _).measurableSet, integral_μ₀, μ₀_real_eq_sum]

namespace StrataExample

/-- The baseline covariate: the prognostic type. -/
def V (ω : Ω₀) : Bool := ω.2.1

/-- The randomized arm: probability `3/4` of the experimental arm in the good stratum and `1/4`
in the poor one. -/
def arm (ω : Ω₀) : Bool := if ω.2.1 then (ω.1 || ω.2.2) else (ω.1 && ω.2.2)

/-- Experimental patients are fully treated with time ratio `1/2`; nobody switches. The
untreated time is `2 s`, with `s = 2` in the good stratum and `1` in the poor one. -/
noncomputable def trial : SwitchingTrial Ω₀ where
  R := arm
  T ω := if arm ω then 4 * scale ω else 2 * scale ω
  Te ω := if arm ω then 4 * scale ω else 0
  U ω := 2 * scale ω

theorem commonEffect : trial.CommonEffect (Real.log (1 / 2)) := by
  intro ω
  obtain ⟨a, u, v⟩ := ω
  rw [Real.exp_log (by norm_num)]
  cases a <;> cases u <;> cases v <;> norm_num [trial, arm, Tc, scale]

/-- The unstratified arm contrast, point by point. -/
theorem meanContrast_eq (X : Ω₀ → ℝ) :
    trial.meanContrast μ₀ X =
      (X (true, true, true) + X (true, true, false) + X (false, true, true) +
          X (true, false, true)) / 4 -
        (X (false, true, false) + X (true, false, false) + X (false, false, true) +
          X (false, false, false)) / 4 := by
  simp only [meanContrast, armMean, integral_cond_μ₀, SwitchingTrial.arm,
    Fintype.sum_prod_type, Fintype.sum_bool, trial, arm]
  simp [arm]
  ring

/-- The arm contrast within the stratum `V = v`, as averages over the points of the stratum in
each arm. -/
theorem stratum_meanContrast_eq (v : Bool) (X : Ω₀ → ℝ) :
    trial.meanContrast μ₀[|V ⁻¹' {v}] X =
      ((∑ ω, (V ⁻¹' {v} ∩ trial.arm true).indicator (1 : Ω₀ → ℝ) ω) / 8)⁻¹ *
          ((∑ ω, (V ⁻¹' {v} ∩ trial.arm true).indicator X ω) / 8) -
        ((∑ ω, (V ⁻¹' {v} ∩ trial.arm false).indicator (1 : Ω₀ → ℝ) ω) / 8)⁻¹ *
          ((∑ ω, (V ⁻¹' {v} ∩ trial.arm false).indicator X ω) / 8) := by
  simp only [meanContrast, armMean]
  rw [cond_cond_eq_cond_inter (Set.toFinite _).measurableSet (Set.toFinite _).measurableSet,
    cond_cond_eq_cond_inter (Set.toFinite _).measurableSet (Set.toFinite _).measurableSet,
    integral_cond_μ₀, integral_cond_μ₀]

/-- **Marginal randomization fails**: the arm contrast of the untreated time is `1`. -/
theorem not_randomized : ¬ trial.Randomized μ₀ := fun hrand ↦ by
  have h := meanContrast_U_of_randomized (measurable_of_finite _) hrand Integrable.of_finite
    (μ₀_ne_zero_of_mem (ω := (true, true, true)) (by simp [SwitchingTrial.arm, trial, arm]))
    (μ₀_ne_zero_of_mem (ω := (false, false, false)) (by simp [SwitchingTrial.arm, trial, arm]))
  rw [meanContrast_eq] at h
  norm_num [trial, scale] at h

/-- **Randomization within strata**: given `V`, the untreated time is constant. -/
theorem randomizedWithin : trial.RandomizedWithin μ₀ V := fun v hv ↦ by
  have hc : (fun _ : Ω₀ ↦ 2 * (if v then (2 : ℝ) else 1)) =ᵐ[μ₀[|V ⁻¹' {v}]] trial.U :=
    (ae_cond_mem (Set.toFinite _).measurableSet).mono fun ω hω ↦ by
      simp only [Set.mem_preimage, Set.mem_singleton_iff, V] at hω
      simp [trial, scale, hω]
  have := cond_isProbabilityMeasure (μ := μ₀) hv
  exact (indepFun_const_right trial.R _).congr (Filter.EventuallyEq.refl _ _) hc

/-- **The unstratified estimating function** is `7 exp ψ - 5/2`. -/
theorem gMean_eq (ψ : ℝ) : trial.gMean μ₀ ψ = 7 * Real.exp ψ - 5 / 2 := by
  rw [gMean, meanContrast_eq]
  simp only [counterfactual, Tc, trial, arm, scale]
  norm_num
  ring

/-- **The unstratified root is wrong**: it is the time ratio `5/14`, not the true `1/2`. -/
theorem unstratified_root (ψ : ℝ) : trial.gMean μ₀ ψ = 0 ↔ Real.exp ψ = 5 / 14 := by
  rw [gMean_eq]
  constructor <;> intro h <;> linarith

/-- The estimating function in the good stratum is `8 exp ψ - 4`. -/
theorem gMean_good (ψ : ℝ) : trial.gMean μ₀[|V ⁻¹' {true}] ψ = 8 * Real.exp ψ - 4 := by
  rw [gMean, stratum_meanContrast_eq]
  simp only [Fintype.sum_prod_type, Fintype.sum_bool]
  simp [V, arm, trial, counterfactual, Tc, scale, SwitchingTrial.arm]
  ring

/-- The estimating function in the poor stratum is `4 exp ψ - 2`. -/
theorem gMean_poor (ψ : ℝ) : trial.gMean μ₀[|V ⁻¹' {false}] ψ = 4 * Real.exp ψ - 2 := by
  rw [gMean, stratum_meanContrast_eq]
  simp only [Fintype.sum_prod_type, Fintype.sum_bool]
  simp [V, arm, trial, counterfactual, Tc, scale, SwitchingTrial.arm]
  ring

/-- The stratified estimating function with unit weights is `12 exp ψ - 6`. -/
theorem stratifiedG_eq (ψ : ℝ) :
    trial.stratifiedG μ₀ V {true, false} (fun _ ↦ 1) ψ = 12 * Real.exp ψ - 6 := by
  rw [stratifiedG, Finset.sum_pair (by decide), gMean_good, gMean_poor]
  ring

/-- **The stratified root is right**: the true parameter `log (1/2)` is the unique root of the
stratified estimating function. -/
theorem stratified_root (ψ : ℝ) :
    trial.stratifiedG μ₀ V {true, false} (fun _ ↦ 1) ψ = 0 ↔ ψ = Real.log (1 / 2) := by
  rw [stratifiedG_eq]
  constructor
  · intro h
    rw [← Real.log_exp ψ, show Real.exp ψ = 1 / 2 by linarith]
  · rintro rfl
    rw [Real.exp_log (by norm_num)]
    norm_num

/-- The unstratified and stratified roots differ. -/
theorem roots_differ : (5 / 14 : ℝ) ≠ Real.exp (Real.log (1 / 2)) := by
  rw [Real.exp_log (by norm_num)]
  norm_num

end StrataExample

namespace ZeroFirstStage

/-- The time on the experimental treatment is `s` in both arms, whatever the arm; observed time
`2 s`. With `ψ = 0` the untreated time is `2 s`. -/
noncomputable def trial : SwitchingTrial Ω₀ where
  R ω := ω.1
  T ω := 2 * scale ω
  Te ω := scale ω
  U ω := 2 * scale ω

/-- The same observed data with `ψ = log (1/2)`: the untreated time is `3 s / 2`. -/
noncomputable def trial' : SwitchingTrial Ω₀ where
  R ω := ω.1
  T ω := 2 * scale ω
  Te ω := scale ω
  U ω := 3 * scale ω / 2

/-- **The same observed data**, hence the same joint law of `(R, T, T^e)`. -/
theorem same_law :
    μ₀.map (fun ω ↦ (trial.R ω, trial.T ω, trial.Te ω)) =
      μ₀.map (fun ω ↦ (trial'.R ω, trial'.T ω, trial'.Te ω)) := rfl

theorem commonEffect : trial.CommonEffect 0 := by
  intro ω
  simp only [trial, Tc, Real.exp_zero]
  ring

theorem commonEffect' : trial'.CommonEffect (Real.log (1 / 2)) := by
  intro ω
  simp only [trial', Tc, Real.exp_log (show (0 : ℝ) < 1 / 2 by norm_num)]
  ring

theorem randomized : trial.Randomized μ₀ :=
  randomized_of_eq trial (fun _ ↦ rfl) (fun p ↦ 2 * if p.1 then 2 else 1) fun _ ↦ rfl

theorem randomized' : trial'.Randomized μ₀ :=
  randomized_of_eq trial' (fun _ ↦ rfl) (fun p ↦ 3 * (if p.1 then 2 else 1) / 2) fun _ ↦ rfl

/-- The first stage is zero. -/
theorem firstStage : trial.meanContrast μ₀ trial.Te = 0 := by
  simp only [meanContrast, armMean_μ₀ trial (fun _ ↦ rfl)]
  simp only [trial, scale]
  norm_num

/-- **A zero first stage does not identify `ψ`.** Two randomized trials with a common effect and
the same law of the observed data `(R, T, T^e)` have the different parameters `0` and
`log (1/2)`. -/
theorem not_identified :
    trial.Randomized μ₀ ∧ trial'.Randomized μ₀ ∧ trial.CommonEffect 0 ∧
      trial'.CommonEffect (Real.log (1 / 2)) ∧
      μ₀.map (fun ω ↦ (trial.R ω, trial.T ω, trial.Te ω)) =
        μ₀.map (fun ω ↦ (trial'.R ω, trial'.T ω, trial'.Te ω)) ∧
      trial.meanContrast μ₀ trial.Te = 0 ∧ (0 : ℝ) ≠ Real.log (1 / 2) :=
  ⟨randomized, randomized', commonEffect, commonEffect', same_law, firstStage,
    (Real.log_neg (by norm_num) (by norm_num)).ne'⟩

end ZeroFirstStage

end StructuralNested

end CausalInference
