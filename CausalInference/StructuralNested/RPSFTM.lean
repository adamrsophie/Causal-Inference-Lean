/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.StructuralNested.FailureTime
public import CausalInference.InstrumentalVariables.LinearIV

/-!
# Randomization-based g-estimation in the RPSFTM

Identification of the parameter `ψ` of the rank preserving structural failure time model
(`CausalInference.StructuralNested.SwitchingTrial`) by randomization, in the population: the
estimating equation of g-estimation and its root. The documents describe g-estimation as
choosing the value of `ψ` for which counterfactual survival is independent of the randomized
group (TSD 16, Appendix A); a g-test (log-rank, Wilcoxon, Wald) compares the candidate
untreated times `U(ψ)` between arms and the estimate is where the test statistic is zero. Here
the population targets of that procedure are formalized: the mean contrast
`ψ ↦ E[U(ψ) | R = 1] - E[U(ψ) | R = 0]` and equality of the arm laws of `U(ψ)`.

## Main definitions

* `SwitchingTrial.affineContrast A B ψ`: the mean contrast of `A + exp ψ B` between arms, for
  observed `A` and `B`; the estimating function of every model in which the untreated time is
  affine in `exp ψ`.
* `SwitchingTrial.gMean ψ`: the mean-form g-estimating function of the RPSFTM, the arm contrast of
  `U(ψ) = T^c + exp ψ T^e`.
* `SwitchingTrial.ArmEffects ψe ψs`: different effects in the experimental arm and in control
  switchers (failure of the common treatment effect).
* `SwitchingTrial.counterfactualMult k ψ`, `SwitchingTrial.gMult k ψ`: the sensitivity analysis
  in which the effect in control switchers is `k ψ` ("psimult", "treat_modifier").
* `SwitchingTrial.enhancedCounterfactual`: the enhanced RPSFTM of TSD 24, Equation (2).

## Main results

* `affineContrast_eq_zero_iff`: in any model `U = A + exp ψ₀ B` with randomization, `ψ₀` is the
  unique root of the mean contrast when the first stage `E[B | R = 1] - E[B | R = 0]` is nonzero.
* `gMean_eq_zero_iff`, `one_sub_exp_eq`: **identification by g-estimation, mean form.** Under the
  common treatment effect and randomization, with integrable `T`, `T^e`, both arms of positive
  probability and a nonzero first stage, `ψ₀` is the unique root of `gMean`, and
  `1 - exp ψ₀ = (E[T | R = 1] - E[T | R = 0]) / (E[T^e | R = 1] - E[T^e | R = 0])`.
* `gMean_eq_zero_of_firstStage_eq_zero`: with a zero first stage every `ψ` is a root (no
  identification), under the model and randomization.
* `armLaw_counterfactual_trueParam`, `eq_trueParam_of_armLaw_eq`: **distributional form.** At
  `ψ₀` the laws of `U(ψ₀)` in the two arms are equal; under a nonzero first stage no other `ψ` has
  equal arm laws.
* `gMean_eq_of_map_eq`: the estimating function depends only on the joint law of the observed
  `(R, T, T^e)` (TSD 16, Section 3.2.2: only randomization, observed survival and observed
  treatment history are used).
* `counterfactual_zero_stat`, `zero_mem_acceptanceSet_iff`: **null preservation.** `U(0) = T`,
  so any statistic of the candidate untreated times at `ψ = 0` is the ITT statistic, and a
  test-inversion confidence set contains `0` exactly when the ITT test does not reject.
* `exp_root_of_armEffects`, `root_lt_of_armEffects`: **bias without a common effect.** If
  experimental patients have parameter `ψe` and control switchers `ψs`, every root `ψ̂` of the
  mean-form equation satisfies
  `exp ψ̂ = exp ψe - (exp ψs - exp ψe) E[T^e | R = 0] / (E[T^e | R = 1] - E[T^e | R = 0])`,
  so the error is proportional to the difference of the time ratios, and switchers who benefit
  less make the method overstate the benefit (TSD 16, Sections 3.2.2, 3.3.1 and 4).
* `gMult_trueParam`, `gMult_eq_zero_iff`: the multiplier sensitivity analysis identifies `ψ₀` at
  the truth; the root is unique when `0 < k ≤ 1`, `E[T^e | R = 1] ≥ 0`, the arm contrast of `T^c`
  is nonpositive, and one of the two monotonicity conditions is strict. Without such a condition
  uniqueness fails (`CausalInference.StructuralNested.RPSFTMCounterexample`).
* `enhancedCounterfactual_eq`, `enhanced_eq_zero_iff`: with `γ = ψ₂ - ψ₁` known, the enhanced
  model is affine in `exp ψ₁`, so `ψ₁` is identified by one-parameter g-estimation.
* `toLinearIV`, `one_sub_exp_eq_covRatio`: the RPSFTM under randomization is an instance of
  `CausalInference.LinearIVModel` with `Y = T`, `D = T^e`, `Z = R` and slope `1 - exp ψ₀`, so
  `1 - exp ψ₀ = Cov(R, T) / Cov(R, T^e)` by `LinearIVModel.beta_eq_covRatio`.

## Setting and scope

Counterfactual variables on a general probability space; real times; no censoring. With
administrative censoring the mean form is not available from the observed data, and the
distributional form must be combined with recensoring. Estimation and testing (log-rank,
Wilcoxon, Wald g-tests, their sampling distributions) are not formalized; only the population
estimating equations and their roots.

## Sources

* N. R. Latimer, K. R. Abrams, *NICE DSU Technical Support Document 16* (2014): Section 3.2.2,
  Section 3.3.1, Section 4, Appendix A ("RPSFTM").
* H. Bell Gorrod, N. R. Latimer, K. R. Abrams, *NICE DSU Technical Support Document 24* (2024):
  Section 4.2.1 (Equation (1), multiple roots), Section 4.2.1.1 (enhanced RPSFTM of Li et al.,
  Equation (2); "Relaxing the common treatment effect assumption").
* J. M. Robins, A. A. Tsiatis, *Correcting for non-compliance in randomized trials using rank
  preserving structural failure time models*, Communications in Statistics: Theory and Methods
  (1991).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set

namespace CausalInference

namespace StructuralNested

namespace SwitchingTrial

variable {Ω : Type*} [MeasurableSpace Ω] {M : SwitchingTrial Ω} {μ : Measure Ω}

/-! ### Affine estimating equations -/

variable (M μ) in
/-- The arm contrast of `A + exp ψ B`, for observed `A` and `B`:
`E[A + exp ψ B | R = true] - E[A + exp ψ B | R = false]`. -/
noncomputable def affineContrast (A B : Ω → ℝ) (ψ : ℝ) : ℝ :=
  M.meanContrast μ fun ω ↦ A ω + Real.exp ψ * B ω

/-- The arm contrast of `A + exp ψ B` is `mc(A) + exp ψ mc(B)`. -/
theorem affineContrast_eq {A B : Ω → ℝ} (hA : Integrable A μ) (hB : Integrable B μ)
    (h1 : μ (M.arm true) ≠ 0) (h0 : μ (M.arm false) ≠ 0) (ψ : ℝ) :
    M.affineContrast μ A B ψ = M.meanContrast μ A + Real.exp ψ * M.meanContrast μ B := by
  have key : ∀ r, μ (M.arm r) ≠ 0 →
      M.armMean μ (fun ω ↦ A ω + Real.exp ψ * B ω) r =
        M.armMean μ A r + Real.exp ψ * M.armMean μ B r := fun r hr ↦ by
    have hA' := Mediation.integrable_cond_of_integrable hA hr
    have hB' := Mediation.integrable_cond_of_integrable hB hr
    simp only [armMean]
    rw [integral_add hA' (hB'.const_mul _), integral_const_mul]
  rw [affineContrast, meanContrast, key true h1, key false h0, meanContrast, meanContrast]
  ring

/-- Under randomization, the untreated time has arm contrast zero. -/
theorem meanContrast_U_of_randomized [IsFiniteMeasure μ] (hR : Measurable M.R)
    (hrand : M.Randomized μ) (hU : Integrable M.U μ) (h1 : μ (M.arm true) ≠ 0)
    (h0 : μ (M.arm false) ≠ 0) : M.meanContrast μ M.U = 0 := by
  rw [meanContrast, armMean_U_of_randomized hR hrand hU h1,
    armMean_U_of_randomized hR hrand hU h0, sub_self]

/-- **Identification in an affine model.** Suppose the untreated time is `U = A + exp ψ₀ B` for
observed integrable `A` and `B`, `U` is independent of the arm, both arms have positive
probability, and the first stage `E[B | R = true] - E[B | R = false]` is nonzero. Then `ψ₀` is the
unique root of `ψ ↦ affineContrast A B ψ`. -/
theorem affineContrast_eq_zero_iff [IsFiniteMeasure μ] (hR : Measurable M.R) {A B : Ω → ℝ}
    {ψ₀ : ℝ} (hmodel : ∀ ω, M.U ω = A ω + Real.exp ψ₀ * B ω) (hrand : M.Randomized μ)
    (hA : Integrable A μ) (hB : Integrable B μ) (h1 : μ (M.arm true) ≠ 0)
    (h0 : μ (M.arm false) ≠ 0) (hrel : M.meanContrast μ B ≠ 0) (ψ : ℝ) :
    M.affineContrast μ A B ψ = 0 ↔ ψ = ψ₀ := by
  have hU : M.U = fun ω ↦ A ω + Real.exp ψ₀ * B ω := funext hmodel
  have hUi : Integrable M.U μ := by rw [hU]; exact hA.add (hB.const_mul _)
  have h₀ : M.affineContrast μ A B ψ₀ = 0 := by
    rw [affineContrast, ← hU]; exact meanContrast_U_of_randomized hR hrand hUi h1 h0
  rw [affineContrast_eq hA hB h1 h0] at h₀ ⊢
  constructor
  · intro h
    have : (Real.exp ψ - Real.exp ψ₀) * M.meanContrast μ B = 0 := by linear_combination h - h₀
    exact Real.exp_injective (sub_eq_zero.1 ((mul_eq_zero.1 this).resolve_right hrel))
  · rintro rfl; exact h₀

/-! ### The RPSFTM: mean form -/

variable (M μ) in
/-- **The mean-form g-estimating function** of the RPSFTM: the arm contrast of the candidate
untreated time, `ψ ↦ E[U(ψ) | R = true] - E[U(ψ) | R = false]`. -/
noncomputable def gMean (ψ : ℝ) : ℝ := M.meanContrast μ (M.counterfactual ψ)

theorem gMean_eq_affineContrast (ψ : ℝ) : M.gMean μ ψ = M.affineContrast μ M.Tc M.Te ψ := rfl

theorem integrable_Tc (hT : Integrable M.T μ) (hTe : Integrable M.Te μ) :
    Integrable M.Tc μ := hT.sub hTe

/-- The arm contrast of `T^c` is that of `T` minus that of `T^e`. -/
theorem meanContrast_Tc (hT : Integrable M.T μ) (hTe : Integrable M.Te μ)
    (h1 : μ (M.arm true) ≠ 0) (h0 : μ (M.arm false) ≠ 0) :
    M.meanContrast μ M.Tc = M.meanContrast μ M.T - M.meanContrast μ M.Te := by
  have key : ∀ r, μ (M.arm r) ≠ 0 → M.armMean μ M.Tc r = M.armMean μ M.T r - M.armMean μ M.Te r :=
    fun r hr ↦ integral_sub (Mediation.integrable_cond_of_integrable hT hr)
      (Mediation.integrable_cond_of_integrable hTe hr)
  rw [meanContrast, key true h1, key false h0, meanContrast, meanContrast]
  ring

/-- `gMean ψ = (mc(T) - mc(T^e)) + exp ψ mc(T^e)`, with `mc` the arm contrast of means. -/
theorem gMean_eq (hT : Integrable M.T μ) (hTe : Integrable M.Te μ) (h1 : μ (M.arm true) ≠ 0)
    (h0 : μ (M.arm false) ≠ 0) (ψ : ℝ) :
    M.gMean μ ψ = (M.meanContrast μ M.T - M.meanContrast μ M.Te) +
      Real.exp ψ * M.meanContrast μ M.Te := by
  rw [gMean_eq_affineContrast, affineContrast_eq (integrable_Tc hT hTe) hTe h1 h0,
    meanContrast_Tc hT hTe h1 h0]

/-- At the true parameter the estimating function vanishes: under the common treatment effect
and randomization, `gMean ψ₀ = 0`. -/
theorem gMean_trueParam [IsFiniteMeasure μ] (hR : Measurable M.R) {ψ₀ : ℝ}
    (h : M.CommonEffect ψ₀) (hrand : M.Randomized μ) (hT : Integrable M.T μ)
    (hTe : Integrable M.Te μ) (h1 : μ (M.arm true) ≠ 0) (h0 : μ (M.arm false) ≠ 0) :
    M.gMean μ ψ₀ = 0 := by
  rw [gMean, ← (M.commonEffect_iff ψ₀).1 h]
  exact meanContrast_U_of_randomized hR hrand (integrable_U_of_commonEffect h hT hTe) h1 h0

/-- **Identification by g-estimation, mean form** (TSD 16, Section 3.2.2 and Appendix A). Under
the common treatment effect `ψ₀`, randomization, integrable `T` and `T^e`, both arms of positive
probability, and a nonzero first stage (randomization changes the mean time on the experimental
treatment), `ψ₀` is the unique root of the mean-form g-estimating function. -/
theorem gMean_eq_zero_iff [IsFiniteMeasure μ] (hR : Measurable M.R) {ψ₀ : ℝ}
    (h : M.CommonEffect ψ₀) (hrand : M.Randomized μ) (hT : Integrable M.T μ)
    (hTe : Integrable M.Te μ) (h1 : μ (M.arm true) ≠ 0) (h0 : μ (M.arm false) ≠ 0)
    (hrel : M.meanContrast μ M.Te ≠ 0) (ψ : ℝ) : M.gMean μ ψ = 0 ↔ ψ = ψ₀ :=
  affineContrast_eq_zero_iff hR (fun ω ↦ h ω) hrand (integrable_Tc hT hTe) hTe
    h1 h0 hrel ψ

/-- **The Wald form of the RPSFTM parameter.** Under the hypotheses of `gMean_eq_zero_iff`,
`1 - exp ψ₀ = (E[T | R = 1] - E[T | R = 0]) / (E[T^e | R = 1] - E[T^e | R = 0])`: the ITT effect
divided by the first stage. -/
theorem one_sub_exp_eq [IsFiniteMeasure μ] (hR : Measurable M.R) {ψ₀ : ℝ}
    (h : M.CommonEffect ψ₀) (hrand : M.Randomized μ) (hT : Integrable M.T μ)
    (hTe : Integrable M.Te μ) (h1 : μ (M.arm true) ≠ 0) (h0 : μ (M.arm false) ≠ 0)
    (hrel : M.meanContrast μ M.Te ≠ 0) :
    1 - Real.exp ψ₀ = M.ittEffect μ / M.meanContrast μ M.Te := by
  have h₀ := gMean_trueParam hR h hrand hT hTe h1 h0
  rw [gMean_eq hT hTe h1 h0] at h₀
  rw [eq_div_iff hrel, ittEffect]
  linear_combination -h₀

/-- **No identification without a first stage.** Under the common treatment effect `ψ₀` and
randomization, if randomization does not change the mean time on the experimental treatment,
every `ψ` is a root of the mean-form estimating function (and the ITT effect is zero). Without
the model and randomization a zero first stage need not give any root. -/
theorem gMean_eq_zero_of_firstStage_eq_zero [IsFiniteMeasure μ] (hR : Measurable M.R)
    {ψ₀ : ℝ} (h : M.CommonEffect ψ₀) (hrand : M.Randomized μ) (hT : Integrable M.T μ)
    (hTe : Integrable M.Te μ) (h1 : μ (M.arm true) ≠ 0) (h0 : μ (M.arm false) ≠ 0)
    (hrel : M.meanContrast μ M.Te = 0) (ψ : ℝ) :
    M.gMean μ ψ = 0 ∧ M.ittEffect μ = 0 := by
  have h₀ := gMean_trueParam hR h hrand hT hTe h1 h0
  rw [gMean_eq hT hTe h1 h0, hrel] at h₀
  rw [gMean_eq hT hTe h1 h0, hrel, ittEffect]
  constructor <;> linarith

/-! ### Distributional form -/

/-- **At the true parameter the arm laws agree.** Under the common treatment effect `ψ₀`,
randomization, measurable `R`, `T`, `T^e` and both arms of positive probability, the law of
`U(ψ₀)` in the experimental arm equals its law in the control arm. -/
theorem armLaw_counterfactual_trueParam [IsFiniteMeasure μ] (hR : Measurable M.R)
    (hTm : Measurable M.T) (hTem : Measurable M.Te) {ψ₀ : ℝ} (h : M.CommonEffect ψ₀)
    (hrand : M.Randomized μ) (h1 : μ (M.arm true) ≠ 0) (h0 : μ (M.arm false) ≠ 0) :
    M.armLaw μ (M.counterfactual ψ₀) true = M.armLaw μ (M.counterfactual ψ₀) false := by
  have hU := (M.commonEffect_iff ψ₀).1 h
  have hUm : Measurable M.U := by rw [hU]; exact measurable_counterfactual hTm hTem ψ₀
  rw [← hU, armLaw_U_of_randomized hR hUm hrand h1, armLaw_U_of_randomized hR hUm hrand h0]

/-- The arm mean of `X` is the mean of its arm law. -/
theorem armMean_eq_integral_armLaw {X : Ω → ℝ} (hX : Measurable X) (r : Bool) :
    M.armMean μ X r = ∫ y, y ∂(M.armLaw μ X r) := by
  rw [armLaw, integral_map hX.aemeasurable (f := fun y : ℝ ↦ y)
    measurable_id'.aestronglyMeasurable]
  rfl

/-- **Uniqueness of the distributional root.** Under the hypotheses of `gMean_eq_zero_iff` and
measurable `T`, `T^e`, any `ψ` at which `U(ψ)` has the same law in both arms is `ψ₀`. So a g-test
that is zero exactly at equal arm laws has a unique population root under a nonzero first stage;
multiple roots come from finite sample statistics (see
`CausalInference.StructuralNested.RPSFTMCounterexample`). -/
theorem eq_trueParam_of_armLaw_eq [IsFiniteMeasure μ] (hR : Measurable M.R)
    (hTm : Measurable M.T) (hTem : Measurable M.Te) {ψ₀ : ℝ} (h : M.CommonEffect ψ₀)
    (hrand : M.Randomized μ) (hT : Integrable M.T μ) (hTe : Integrable M.Te μ)
    (h1 : μ (M.arm true) ≠ 0) (h0 : μ (M.arm false) ≠ 0) (hrel : M.meanContrast μ M.Te ≠ 0)
    {ψ : ℝ} (hlaw : M.armLaw μ (M.counterfactual ψ) true = M.armLaw μ (M.counterfactual ψ) false) :
    ψ = ψ₀ := by
  refine (gMean_eq_zero_iff hR h hrand hT hTe h1 h0 hrel ψ).1 ?_
  have hm := measurable_counterfactual hTm hTem ψ
  rw [gMean, meanContrast, armMean_eq_integral_armLaw hm, armMean_eq_integral_armLaw hm, hlaw,
    sub_self]

/-! ### Dependence on the observed data only -/

/-- The arm mean of `f (T, T^e)` depends only on the joint law of `(R, T, T^e)`. -/
theorem armMean_comp_eq_of_map_eq {Ω' : Type*} [MeasurableSpace Ω'] {M' : SwitchingTrial Ω'}
    {μ' : Measure Ω'} (hR : Measurable M.R) (hT : Measurable M.T) (hTe : Measurable M.Te)
    (hR' : Measurable M'.R) (hT' : Measurable M'.T) (hTe' : Measurable M'.Te)
    (hlaw : μ.map (fun ω ↦ (M.R ω, M.T ω, M.Te ω)) =
      μ'.map (fun ω ↦ (M'.R ω, M'.T ω, M'.Te ω)))
    {f : ℝ × ℝ → ℝ} (hf : Measurable f) (r : Bool) :
    M.armMean μ (fun ω ↦ f (M.T ω, M.Te ω)) r =
      M'.armMean μ' (fun ω ↦ f (M'.T ω, M'.Te ω)) r := by
  have hS : MeasurableSet (({r} : Set Bool) ×ˢ (univ : Set (ℝ × ℝ))) :=
    (measurableSet_singleton r).prod MeasurableSet.univ
  have hg : Measurable fun x : Bool × ℝ × ℝ ↦ f x.2 := hf.comp measurable_snd
  have hO := hR.prodMk (hT.prodMk hTe)
  have hO' := hR'.prodMk (hT'.prodMk hTe')
  have p1 : (fun ω ↦ (M.R ω, M.T ω, M.Te ω)) ⁻¹' (({r} : Set Bool) ×ˢ (univ : Set (ℝ × ℝ))) =
      M.R ⁻¹' {r} := by ext; simp
  have p2 : (fun ω ↦ (M'.R ω, M'.T ω, M'.Te ω)) ⁻¹' (({r} : Set Bool) ×ˢ (univ : Set (ℝ × ℝ))) =
      M'.R ⁻¹' {r} := by ext; simp
  have e1 : M.armMean μ (fun ω ↦ f (M.T ω, M.Te ω)) r =
      (μ.map (fun ω ↦ (M.R ω, M.T ω, M.Te ω)) ({r} ×ˢ univ)).toReal⁻¹ *
        ∫ x in ({r} : Set Bool) ×ˢ (univ : Set (ℝ × ℝ)), f x.2
          ∂(μ.map (fun ω ↦ (M.R ω, M.T ω, M.Te ω))) := by
    rw [setIntegral_map hS hg.aestronglyMeasurable hO.aemeasurable, Measure.map_apply hO hS,
      p1, armMean, ← Mediation.condMean, Mediation.condMean_eq, measureReal_def]
    rfl
  have e2 : M'.armMean μ' (fun ω ↦ f (M'.T ω, M'.Te ω)) r =
      (μ'.map (fun ω ↦ (M'.R ω, M'.T ω, M'.Te ω)) ({r} ×ˢ univ)).toReal⁻¹ *
        ∫ x in ({r} : Set Bool) ×ˢ (univ : Set (ℝ × ℝ)), f x.2
          ∂(μ'.map (fun ω ↦ (M'.R ω, M'.T ω, M'.Te ω))) := by
    rw [setIntegral_map hS hg.aestronglyMeasurable hO'.aemeasurable, Measure.map_apply hO' hS,
      p2, armMean, ← Mediation.condMean, Mediation.condMean_eq, measureReal_def]
    rfl
  rw [e1, e2, hlaw]

/-- **The estimating function uses only randomization, observed survival and observed treatment
history** (TSD 16, Section 3.2.2). Two trials, possibly on different sample spaces and with
different latent untreated times, whose observed data `(R, T, T^e)` have the same joint law have
the same mean-form g-estimating function. -/
theorem gMean_eq_of_map_eq {Ω' : Type*} [MeasurableSpace Ω'] {M' : SwitchingTrial Ω'}
    {μ' : Measure Ω'} (hR : Measurable M.R) (hT : Measurable M.T) (hTe : Measurable M.Te)
    (hR' : Measurable M'.R) (hT' : Measurable M'.T) (hTe' : Measurable M'.Te)
    (hlaw : μ.map (fun ω ↦ (M.R ω, M.T ω, M.Te ω)) =
      μ'.map (fun ω ↦ (M'.R ω, M'.T ω, M'.Te ω))) (ψ : ℝ) :
    M.gMean μ ψ = M'.gMean μ' ψ := by
  have hf : Measurable fun x : ℝ × ℝ ↦ x.1 - x.2 + Real.exp ψ * x.2 := by fun_prop
  have k := fun r ↦ armMean_comp_eq_of_map_eq hR hT hTe hR' hT' hTe' hlaw hf r
  simp only [gMean, meanContrast]
  exact congrArg₂ (· - ·) (k true) (k false)

/-! ### Null preservation -/

omit [MeasurableSpace Ω] in
/-- **The g-test at `ψ = 0` is the ITT test** (TSD 16, Appendix A: the RPSFTM maintains the ITT
p-value). Since `U(0) = T`, any statistic of the candidate untreated times at `ψ = 0` equals that
statistic applied to the observed times. -/
theorem counterfactual_zero_stat {β : Type*} (Φ : (Ω → ℝ) → β) :
    Φ (M.counterfactual 0) = Φ M.T := by
  rw [counterfactual_zero]

/-- The test-inversion confidence set of a g-test: the parameters at which the statistic `Φ` of
the candidate untreated times lies in the acceptance region `A`. -/
def acceptanceSet {β : Type*} (Φ : (Ω → ℝ) → β) (A : Set β) : Set ℝ :=
  {ψ | Φ (M.counterfactual ψ) ∈ A}

omit [MeasurableSpace Ω] in
/-- The g-test confidence set contains `ψ = 0` exactly when the ITT test with the same statistic
and acceptance region does not reject. -/
theorem zero_mem_acceptanceSet_iff {β : Type*} (Φ : (Ω → ℝ) → β) (A : Set β) :
    0 ∈ M.acceptanceSet Φ A ↔ Φ M.T ∈ A := by
  rw [acceptanceSet, mem_ofPred_eq, counterfactual_zero]

/-! ### Failure of the common treatment effect -/

variable (M) in
/-- **Arm specific effects.** Experimental patients have parameter `ψe`, control patients (who
receive the experimental treatment only by switching) have `ψs`. -/
def ArmEffects (ψe ψs : ℝ) : Prop := M.FollowsModel fun ω ↦ if M.R ω then ψe else ψs

/-- Under arm specific effects, the arm mean of `U` in arm `r` is that of `U(ψ_r)`. -/
theorem armMean_U_of_armEffects (hR : Measurable M.R) {ψe ψs : ℝ} (h : M.ArmEffects ψe ψs)
    (r : Bool) :
    M.armMean μ M.U r = M.armMean μ (M.counterfactual (if r then ψe else ψs)) r := by
  refine integral_congr_ae ?_
  filter_upwards [ae_cond_mem (M.measurableSet_arm hR r)] with ω hω
  have hr : M.R ω = r := hω
  rw [h ω]; simp only [hr]; rfl

/-- **The RPSFTM root without a common effect** (TSD 16, Sections 3.2.2 and 3.3.1). Suppose
experimental patients have parameter `ψe` and control switchers `ψs`, `U` is independent of the
arm, `T`, `T^e`, `U` are integrable, both arms have positive probability and the first stage is
nonzero. Then every root `ψ̂` of the one-parameter mean-form equation satisfies
`exp ψ̂ = exp ψe - (exp ψs - exp ψe) E[T^e | R = 0] / (E[T^e | R = 1] - E[T^e | R = 0])`.
A root need not exist (the right side can be nonpositive). -/
theorem exp_root_of_armEffects [IsFiniteMeasure μ] (hR : Measurable M.R) {ψe ψs : ℝ}
    (h : M.ArmEffects ψe ψs) (hrand : M.Randomized μ) (hT : Integrable M.T μ)
    (hTe : Integrable M.Te μ) (hU : Integrable M.U μ) (h1 : μ (M.arm true) ≠ 0)
    (h0 : μ (M.arm false) ≠ 0) (hrel : M.meanContrast μ M.Te ≠ 0) {ψ : ℝ}
    (hroot : M.gMean μ ψ = 0) :
    Real.exp ψ = Real.exp ψe -
      (Real.exp ψs - Real.exp ψe) * M.armMean μ M.Te false / M.meanContrast μ M.Te := by
  have e1 := armMean_U_of_armEffects (μ := μ) hR h true
  have e0 := armMean_U_of_armEffects (μ := μ) hR h false
  rw [armMean_U_of_randomized hR hrand hU h1, armMean_counterfactual hT hTe h1] at e1
  rw [armMean_U_of_randomized hR hrand hU h0, armMean_counterfactual hT hTe h0] at e0
  simp only [ite_true, Bool.false_eq_true, ite_false] at e1 e0
  rw [gMean_eq hT hTe h1 h0] at hroot
  have key : Real.exp ψ * M.meanContrast μ M.Te = Real.exp ψe * M.meanContrast μ M.Te -
      (Real.exp ψs - Real.exp ψe) * M.armMean μ M.Te false := by
    simp only [meanContrast] at hroot ⊢
    linear_combination hroot + e1 - e0
  have : (Real.exp ψs - Real.exp ψe) * M.armMean μ M.Te false / M.meanContrast μ M.Te =
      Real.exp ψe - Real.exp ψ := by
    rw [div_eq_iff hrel]; linear_combination key
  linarith

/-- **Switchers who benefit less make the RPSFTM overstate the benefit** (TSD 16, Section 4: the
bias is driven by the difference of the acceleration factors). Under the hypotheses of
`exp_root_of_armEffects`, if `ψe < ψs` (a smaller benefit in switchers when both are negative)
and `0 < E[T^e | R = 0] < E[T^e | R = 1]`, then every root satisfies `ψ̂ < ψe`. -/
theorem root_lt_of_armEffects [IsFiniteMeasure μ] (hR : Measurable M.R) {ψe ψs : ℝ}
    (h : M.ArmEffects ψe ψs) (hrand : M.Randomized μ) (hT : Integrable M.T μ)
    (hTe : Integrable M.Te μ) (hU : Integrable M.U μ) (h1 : μ (M.arm true) ≠ 0)
    (h0 : μ (M.arm false) ≠ 0) (hs : ψe < ψs) (hb0 : 0 < M.armMean μ M.Te false)
    (hb : M.armMean μ M.Te false < M.armMean μ M.Te true) {ψ : ℝ} (hroot : M.gMean μ ψ = 0) :
    ψ < ψe := by
  have hpos : 0 < M.meanContrast μ M.Te := by rw [meanContrast]; linarith
  have e := exp_root_of_armEffects hR h hrand hT hTe hU h1 h0 hpos.ne' hroot
  have hd : 0 < Real.exp ψs - Real.exp ψe := sub_pos.2 (Real.exp_lt_exp.2 hs)
  have : 0 < (Real.exp ψs - Real.exp ψe) * M.armMean μ M.Te false / M.meanContrast μ M.Te :=
    div_pos (mul_pos hd hb0) hpos
  exact Real.exp_lt_exp.1 (by linarith)

/-! ### Sensitivity analysis with a known multiplier -/

variable (M) in
/-- The candidate untreated time when the effect in the control arm is `k` times the effect in
the experimental arm ("psimult(k)" of strbee, "treat_modifier(k)" of rpsftm; TSD 24,
Section 4.2.1.1): `U_k(ψ) = T^c + exp (k_R ψ) T^e` with `k_true = 1` and `k_false = k`. -/
noncomputable def counterfactualMult (k ψ : ℝ) (ω : Ω) : ℝ :=
  M.Tc ω + Real.exp ((if M.R ω then 1 else k) * ψ) * M.Te ω

variable (M μ) in
/-- The mean-form estimating function of the multiplier analysis. -/
noncomputable def gMult (k ψ : ℝ) : ℝ := M.meanContrast μ (M.counterfactualMult k ψ)

variable (M) in
/-- The model of the multiplier analysis: `U = U_k(ψ₀)`, the effect in control switchers is
`k ψ₀`. -/
def MultiplierModel (k ψ₀ : ℝ) : Prop := M.FollowsModel fun ω ↦ (if M.R ω then 1 else k) * ψ₀

/-- The multiplier estimating function in terms of arm means:
`gMult k ψ = mc(T^c) + exp ψ E[T^e | R = 1] - exp (k ψ) E[T^e | R = 0]`. -/
theorem gMult_eq (hR : Measurable M.R) (hT : Integrable M.T μ) (hTe : Integrable M.Te μ)
    (h1 : μ (M.arm true) ≠ 0) (h0 : μ (M.arm false) ≠ 0) (k ψ : ℝ) :
    M.gMult μ k ψ = M.meanContrast μ M.Tc + Real.exp ψ * M.armMean μ M.Te true -
      Real.exp (k * ψ) * M.armMean μ M.Te false := by
  have key : ∀ r, μ (M.arm r) ≠ 0 → M.armMean μ (M.counterfactualMult k ψ) r =
      M.armMean μ M.Tc r + Real.exp ((if r then 1 else k) * ψ) * M.armMean μ M.Te r :=
    fun r hr ↦ by
      have e : M.armMean μ (M.counterfactualMult k ψ) r =
          M.armMean μ (fun ω ↦ M.Tc ω + Real.exp ((if r then 1 else k) * ψ) * M.Te ω) r := by
        refine integral_congr_ae ?_
        filter_upwards [ae_cond_mem (M.measurableSet_arm hR r)] with ω hω
        have hr : M.R ω = r := hω
        simp only [counterfactualMult, hr]
      have hc := Mediation.integrable_cond_of_integrable (integrable_Tc hT hTe) hr
      have hTe' := Mediation.integrable_cond_of_integrable hTe hr
      rw [e, armMean, integral_add hc (hTe'.const_mul _), integral_const_mul]
      rfl
  rw [gMult, meanContrast, key true h1, key false h0, meanContrast]
  simp only [ite_true, Bool.false_eq_true, ite_false, one_mul]
  ring

/-- **The multiplier analysis is right at the truth.** Under the multiplier model with known
`k`, randomization, integrable `T`, `T^e`, `U` and both arms of positive probability,
`gMult k ψ₀ = 0`. -/
theorem gMult_trueParam [IsFiniteMeasure μ] (hR : Measurable M.R) {k ψ₀ : ℝ}
    (h : M.MultiplierModel k ψ₀) (hrand : M.Randomized μ) (hU : Integrable M.U μ)
    (h1 : μ (M.arm true) ≠ 0) (h0 : μ (M.arm false) ≠ 0) : M.gMult μ k ψ₀ = 0 := by
  have hU' : M.U = M.counterfactualMult k ψ₀ := funext fun ω ↦ h ω
  rw [gMult, ← hU']
  exact meanContrast_U_of_randomized hR hrand hU h1 h0

/-- **Uniqueness of the multiplier root under a monotonicity condition** (a sufficient condition
found here; the documents state none). Under the hypotheses of `gMult_trueParam` and integrable
`T`, `T^e`, suppose `0 < k ≤ 1`, `E[T^e | R = 1] ≥ 0`, the arm contrast of the time off the
experimental treatment `E[T^c | R = 1] - E[T^c | R = 0]` is nonpositive, and either it is negative
or `k < 1` and `E[T^e | R = 1] > 0`. Then `ψ₀` is the unique root of `gMult k`. The proof: after
division by `exp (k ψ)` the estimating function is strictly increasing. -/
theorem gMult_eq_zero_iff [IsFiniteMeasure μ] (hR : Measurable M.R) {k ψ₀ : ℝ}
    (h : M.MultiplierModel k ψ₀) (hrand : M.Randomized μ) (hT : Integrable M.T μ)
    (hTe : Integrable M.Te μ) (hU : Integrable M.U μ) (h1 : μ (M.arm true) ≠ 0)
    (h0 : μ (M.arm false) ≠ 0) (hk0 : 0 < k) (hk1 : k ≤ 1)
    (hb1 : 0 ≤ M.armMean μ M.Te true) (hc : M.meanContrast μ M.Tc ≤ 0)
    (hstrict : M.meanContrast μ M.Tc < 0 ∨ (k < 1 ∧ 0 < M.armMean μ M.Te true)) (ψ : ℝ) :
    M.gMult μ k ψ = 0 ↔ ψ = ψ₀ := by
  set c := M.meanContrast μ M.Tc
  set b1 := M.armMean μ M.Te true
  set b0 := M.armMean μ M.Te false
  let F : ℝ → ℝ := fun x ↦ c * Real.exp (-(k * x)) + b1 * Real.exp ((1 - k) * x) - b0
  have hF : ∀ x, M.gMult μ k x = Real.exp (k * x) * F x := fun x ↦ by
    have ea : Real.exp (k * x) * Real.exp (-(k * x)) = 1 := by
      rw [← Real.exp_add]; simp
    have eb : Real.exp (k * x) * Real.exp ((1 - k) * x) = Real.exp x := by
      rw [← Real.exp_add]; ring_nf
    rw [gMult_eq hR hT hTe h1 h0]
    simp only [F]
    linear_combination (-c) * ea - b1 * eb
  have hmono : StrictMono F := by
    intro x y hxy
    have e1 : Real.exp (-(k * y)) < Real.exp (-(k * x)) :=
      Real.exp_lt_exp.2 (by nlinarith)
    have e2 : Real.exp ((1 - k) * x) ≤ Real.exp ((1 - k) * y) :=
      Real.exp_le_exp.2 (by nlinarith)
    have t1 : c * Real.exp (-(k * x)) ≤ c * Real.exp (-(k * y)) :=
      mul_le_mul_of_nonpos_left e1.le hc
    have t2 : b1 * Real.exp ((1 - k) * x) ≤ b1 * Real.exp ((1 - k) * y) :=
      mul_le_mul_of_nonneg_left e2 hb1
    simp only [F]
    rcases hstrict with hcneg | ⟨hk, hb⟩
    · have : c * Real.exp (-(k * x)) < c * Real.exp (-(k * y)) :=
        mul_lt_mul_of_neg_left e1 hcneg
      linarith
    · have e2' : Real.exp ((1 - k) * x) < Real.exp ((1 - k) * y) :=
        Real.exp_lt_exp.2 (by nlinarith)
      have : b1 * Real.exp ((1 - k) * x) < b1 * Real.exp ((1 - k) * y) :=
        mul_lt_mul_of_pos_left e2' hb
      linarith
  have hroot : ∀ x, M.gMult μ k x = 0 ↔ F x = 0 := fun x ↦ by
    rw [hF x]; exact ⟨fun h ↦ (mul_eq_zero.1 h).resolve_left (Real.exp_pos _).ne',
      fun h ↦ by rw [h, mul_zero]⟩
  have h₀ : F ψ₀ = 0 := (hroot ψ₀).1 (gMult_trueParam hR h hrand hU h1 h0)
  rw [hroot ψ]
  exact ⟨fun hψ ↦ hmono.injective (hψ.trans h₀.symm), fun hψ ↦ hψ ▸ h₀⟩

/-! ### The enhanced RPSFTM of Li et al. with known `γ` -/

variable (M) in
/-- **The enhanced RPSFTM, TSD 24 Equation (2)** (Li et al. 2017). With progression time
`TPFS`, treatment at randomization `Z⁰ = R` (coded `1` for the experimental arm) and treatment
after progression `ZP` (`0` none, `1` experimental, `2` an alternative treatment):
`U(ψ₁, ψ₂) = TPFS exp (Z⁰ ψ₁) + (T - TPFS) exp (1{ZP = 2} ψ₂ + 1{ZP = 1} ψ₁)`. -/
noncomputable def enhancedCounterfactual (TPFS : Ω → ℝ) (ZP : Ω → Fin 3) (ψ₁ ψ₂ : ℝ)
    (ω : Ω) : ℝ :=
  TPFS ω * Real.exp ((if M.R ω then 1 else 0) * ψ₁) +
    (M.T ω - TPFS ω) *
      Real.exp ((if ZP ω = 2 then 1 else 0) * ψ₂ + (if ZP ω = 1 then 1 else 0) * ψ₁)

variable (M) in
/-- The part of the enhanced counterfactual that does not scale with `exp ψ₁`. -/
noncomputable def enhancedA (TPFS : Ω → ℝ) (ZP : Ω → Fin 3) (ω : Ω) : ℝ :=
  (if M.R ω then 0 else TPFS ω) + (if ZP ω = 0 then M.T ω - TPFS ω else 0)

variable (M) in
/-- The part of the enhanced counterfactual that scales with `exp ψ₁`, for known `γ`. -/
noncomputable def enhancedB (TPFS : Ω → ℝ) (ZP : Ω → Fin 3) (γ : ℝ) (ω : Ω) : ℝ :=
  (if M.R ω then TPFS ω else 0) + (if ZP ω = 1 then M.T ω - TPFS ω else 0) +
    (if ZP ω = 2 then Real.exp γ * (M.T ω - TPFS ω) else 0)

omit [MeasurableSpace Ω] in
/-- With `ψ₂ = ψ₁ + γ` the enhanced counterfactual is affine in `exp ψ₁`. -/
theorem enhancedCounterfactual_eq (TPFS : Ω → ℝ) (ZP : Ω → Fin 3) (ψ₁ γ : ℝ) (ω : Ω) :
    M.enhancedCounterfactual TPFS ZP ψ₁ (ψ₁ + γ) ω =
      M.enhancedA TPFS ZP ω + Real.exp ψ₁ * M.enhancedB TPFS ZP γ ω := by
  simp only [enhancedCounterfactual, enhancedA, enhancedB]
  rcases (show ∀ i : Fin 3, i = 0 ∨ i = 1 ∨ i = 2 by decide) (ZP ω) with h | h | h <;>
    cases M.R ω <;> simp [h, Real.exp_add] <;> ring

/-- **Identification of `ψ₁` in the enhanced RPSFTM with known `γ`** (TSD 24,
Section 4.2.1.1). If `U = U(ψ₁⁰, ψ₁⁰ + γ)` for a known `γ = ψ₂ - ψ₁`, `U` is independent of the
arm, the two parts `enhancedA`, `enhancedB` are integrable, both arms have positive probability
and the first stage of `enhancedB` is nonzero, then `ψ₁⁰` is the unique root of the
one-parameter estimating function `ψ ↦ mc(U(ψ, ψ + γ))`. The estimation of `γ` itself (a Weibull
model under no unmeasured confounding) is not formalized. -/
theorem enhanced_eq_zero_iff [IsFiniteMeasure μ] (hR : Measurable M.R) {TPFS : Ω → ℝ}
    {ZP : Ω → Fin 3} {γ ψ₀ : ℝ}
    (hmodel : ∀ ω, M.U ω = M.enhancedCounterfactual TPFS ZP ψ₀ (ψ₀ + γ) ω)
    (hrand : M.Randomized μ) (hA : Integrable (M.enhancedA TPFS ZP) μ)
    (hB : Integrable (M.enhancedB TPFS ZP γ) μ) (h1 : μ (M.arm true) ≠ 0)
    (h0 : μ (M.arm false) ≠ 0) (hrel : M.meanContrast μ (M.enhancedB TPFS ZP γ) ≠ 0) (ψ : ℝ) :
    M.meanContrast μ (M.enhancedCounterfactual TPFS ZP ψ (ψ + γ)) = 0 ↔ ψ = ψ₀ := by
  have e : M.enhancedCounterfactual TPFS ZP ψ (ψ + γ) =
      fun ω ↦ M.enhancedA TPFS ZP ω + Real.exp ψ * M.enhancedB TPFS ZP γ ω :=
    funext (enhancedCounterfactual_eq TPFS ZP ψ γ)
  rw [e]
  exact affineContrast_eq_zero_iff hR (fun ω ↦ by rw [hmodel, enhancedCounterfactual_eq])
    hrand hA hB h1 h0 hrel ψ

/-! ### The bridge to the linear instrumental variable model -/

variable (M μ) in
/-- The linear instrumental variable model of a switching trial (TSD 16, Section 3.2.2: the
RPSFTM is an instrumental variable method with the randomized group as instrument): outcome
`Y = T`, treatment `D = T^e`, instrument `Z = R` coded `0`/`1`, slope `β = 1 - exp ψ`,
intercept `α = E[U]` and structural error `U - E[U]`. -/
noncomputable def toLinearIV (ψ : ℝ) : LinearIVModel Ω where
  α := ∫ ω, M.U ω ∂μ
  β := 1 - Real.exp ψ
  D := M.Te
  Z ω := IVModel.boolToReal (M.R ω)
  U ω := M.U ω + -∫ ω, M.U ω ∂μ

/-- Under the common treatment effect `ψ`, the outcome of `toLinearIV ψ` is the observed time. -/
theorem toLinearIV_Y {ψ : ℝ} (h : M.CommonEffect ψ) : (M.toLinearIV μ ψ).Y = M.T := by
  funext ω
  simp only [LinearIVModel.Y, toLinearIV, M.T_eq_of_commonEffect h ω]
  ring

/-- Randomization gives exogeneity of the instrument in `toLinearIV ψ`, for square integrable
`U` and measurable `R`. -/
theorem toLinearIV_exogeneity [IsProbabilityMeasure μ] (hR : Measurable M.R)
    (hrand : M.Randomized μ) (hU : MemLp M.U 2 μ) (ψ : ℝ) :
    (M.toLinearIV μ ψ).Exogeneity μ := by
  have hZ : MemLp (fun ω ↦ IVModel.boolToReal (M.R ω)) 2 μ :=
    MemLp.of_bound (IVModel.measurable_boolToReal.comp hR).aestronglyMeasurable 1
      (ae_of_all _ fun ω ↦ by cases M.R ω <;> simp [IVModel.boolToReal])
  have hind : IndepFun (fun ω ↦ IVModel.boolToReal (M.R ω)) M.U μ :=
    hrand.comp IVModel.measurable_boolToReal measurable_id
  simp only [LinearIVModel.Exogeneity, toLinearIV]
  rw [covariance_add_const_right (hU.integrable one_le_two)]
  exact hind.covariance_eq_zero hZ hU

/-- **The RPSFTM parameter as a linear IV estimand** (TSD 16, Section 3.2.2). Under the
common treatment effect `ψ₀`, randomization, measurable `R`, square integrable `T` and `T^e`, and
a relevant instrument `Cov(R, T^e) ≠ 0`, `1 - exp ψ₀ = Cov(R, T) / Cov(R, T^e)`. This is
`LinearIVModel.beta_eq_covRatio` for `toLinearIV ψ₀`; for the binary instrument the ratio is the
Wald ratio of `one_sub_exp_eq` (`LinearIV.covRatio_eq_waldRatio`). -/
theorem one_sub_exp_eq_covRatio [IsProbabilityMeasure μ] (hR : Measurable M.R) {ψ₀ : ℝ}
    (h : M.CommonEffect ψ₀) (hrand : M.Randomized μ) (hT : MemLp M.T 2 μ)
    (hTe : MemLp M.Te 2 μ)
    (hrel : cov[fun ω ↦ IVModel.boolToReal (M.R ω), M.Te; μ] ≠ 0) :
    1 - Real.exp ψ₀ =
      cov[fun ω ↦ IVModel.boolToReal (M.R ω), M.T; μ] /
        cov[fun ω ↦ IVModel.boolToReal (M.R ω), M.Te; μ] := by
  have hU : MemLp M.U 2 μ := by
    rw [(M.commonEffect_iff ψ₀).1 h]
    exact (hT.sub hTe).add (hTe.const_mul _)
  have hZ : MemLp (fun ω ↦ IVModel.boolToReal (M.R ω)) 2 μ :=
    MemLp.of_bound (IVModel.measurable_boolToReal.comp hR).aestronglyMeasurable 1
      (ae_of_all _ fun ω ↦ by cases M.R ω <;> simp [IVModel.boolToReal])
  have hsm : (M.toLinearIV μ ψ₀).SecondMoments μ :=
    ⟨hTe, hZ, hU.add (memLp_const _)⟩
  have := LinearIVModel.beta_eq_covRatio hsm (toLinearIV_exogeneity hR hrand hU ψ₀) hrel
  rw [toLinearIV_Y h] at this
  exact this

end SwitchingTrial

end StructuralNested

end CausalInference
