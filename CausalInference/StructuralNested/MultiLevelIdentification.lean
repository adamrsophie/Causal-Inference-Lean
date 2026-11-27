/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.StructuralNested.RPSFTMExtensions

/-!
# Identification of the model with several treatment levels

The model with one parameter per treatment level (TSD 24, Section 4.2.1.1) is not identified by
one binary randomization, even in the distributional form; strata of a baseline variable with
randomization within strata identify it exactly when the matrix of first stages is injective.

## Main definitions

* `MultiLevelTrial.refCounterfactual M T₀ ψ = T₀ + Σ_k exp (ψ_k) T_k`: the untreated time with a
  reference time `T₀` (time off all treatments, time ratio fixed at `1`) and one parameter per
  treatment level; `MultiLevelTrial.RefModel` is the structural model at `ψ`.
* `MultiLevelTrial.firstStageMatrix μ V`: the matrix whose entry `(s, k)` is the first stage
  `E[T_k | R = 1, V = s] - E[T_k | R = 0, V = s]` of level `k` in stratum `s`.

## Main results

* `DistributionalExample.not_identified`: a trial on a finite space with three levels, the model
  at `ψ₀ = (0, 0, 0)` and the arm independent of the untreated time, in which the candidate
  untreated time at `ψ = (0, log 2, log 3) ≠ ψ₀` has the same law in the two arms. So no test
  comparing the two arms' laws of `U(ψ)` (in particular no rank test) separates `ψ` from `ψ₀`.
* `MultiLevelTrial.identified_iff_injective`: with randomization within the strata of a baseline
  variable `V` (`SwitchingTrial.RandomizedWithin`), the true parameter is the unique solution of
  the stratum mean restrictions if and only if `firstStageMatrix μ V` is injective as a map on
  the exponentiated parameters, for any finite set of levels and any set of strata.
* `MultiLevelTrial.identified_iff_det_ne_zero`: for two levels on top of the reference level and
  two strata, the true parameter is identified if and only if the determinant of the two by two
  matrix of first stages is nonzero; `MultiLevelTrial.not_identified_of_det_eq_zero`: when it is
  zero there is another solution.

## Sources

H. Bell Gorrod, N. R. Latimer, K. R. Abrams, *NICE DSU Technical Support Document 24* (2024),
Section 4.2.1.1.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set Filter Topology Matrix

namespace CausalInference

namespace StructuralNested

namespace MultiLevelTrial

variable {Ω ι : Type*} [Fintype ι]

/-- The untreated time with a reference time `T₀` and one parameter per level:
`T₀ + Σ_k exp (ψ_k) T_k`. -/
noncomputable def refCounterfactual (M : MultiLevelTrial Ω ι) (T₀ : Ω → ℝ) (ψ : ι → ℝ)
    (ω : Ω) : ℝ :=
  T₀ ω + M.counterfactual ψ ω

/-- The structural model with reference time `T₀` at the parameter vector `ψ`. -/
def RefModel (M : MultiLevelTrial Ω ι) (T₀ : Ω → ℝ) (ψ : ι → ℝ) : Prop :=
  ∀ ω, M.U ω = M.refCounterfactual T₀ ψ ω

/-- The arm and the untreated time as a `SwitchingTrial` (the other fields are not used), so that
`SwitchingTrial.RandomizedWithin` applies. -/
def toSwitchingTrial (M : MultiLevelTrial Ω ι) : SwitchingTrial Ω where
  R := M.R
  T := M.U
  Te := 0
  U := M.U

variable [MeasurableSpace Ω] {M : MultiLevelTrial Ω ι}

/-- The matrix of first stages: entry `(s, k)` is the arm contrast of `T_k` in stratum `s`. -/
noncomputable def firstStageMatrix (M : MultiLevelTrial Ω ι) (μ : Measure Ω) {β : Type*}
    (V : Ω → β) : Matrix β ι ℝ :=
  fun s k ↦ M.meanContrast μ[|V ⁻¹' {s}] (M.Tk k)

/-- The mean restriction with a reference time is one affine equation in the `exp (ψ_k)`. -/
theorem meanContrast_refCounterfactual {ν : Measure Ω} {T₀ : Ω → ℝ} (h₀ : Integrable T₀ ν)
    (hT : ∀ k, Integrable (M.Tk k) ν) (h1 : ν (M.R ⁻¹' {true}) ≠ 0)
    (h0 : ν (M.R ⁻¹' {false}) ≠ 0) (ψ : ι → ℝ) :
    M.meanContrast ν (M.refCounterfactual T₀ ψ) =
      M.meanContrast ν T₀ + ∑ k, Real.exp (ψ k) * M.meanContrast ν (M.Tk k) := by
  have hcf : ∀ r, ν (M.R ⁻¹' {r}) ≠ 0 →
      Integrable (M.counterfactual ψ) ν[|M.R ⁻¹' {r}] := fun r hr ↦
    integrable_finsetSum _ fun k _ ↦
      (Mediation.integrable_cond_of_integrable (hT k) hr).const_mul _
  have e := meanContrast_eq hT h1 h0 ψ
  simp only [meanContrast, refCounterfactual] at e ⊢
  rw [integral_add (Mediation.integrable_cond_of_integrable h₀ h1) (hcf true h1),
    integral_add (Mediation.integrable_cond_of_integrable h₀ h0) (hcf false h0), ← e]
  ring

/-- The true parameter satisfies the mean restriction under any finite measure in which the arm
is independent of the untreated time. -/
theorem meanContrast_refCounterfactual_trueParam {ν : Measure Ω} [IsFiniteMeasure ν]
    (hR : Measurable M.R) {T₀ : Ω → ℝ} {ψ₀ : ι → ℝ} (h : M.RefModel T₀ ψ₀)
    (hrand : IndepFun M.R M.U ν) (hU : Integrable M.U ν) (h1 : ν (M.R ⁻¹' {true}) ≠ 0)
    (h0 : ν (M.R ⁻¹' {false}) ≠ 0) : M.meanContrast ν (M.refCounterfactual T₀ ψ₀) = 0 := by
  have hU' : M.refCounterfactual T₀ ψ₀ = M.U := (funext h).symm
  have e1 := Mediation.condMean_preimage_singleton_of_indepFun hrand.symm hR hU h1
  have e0 := Mediation.condMean_preimage_singleton_of_indepFun hrand.symm hR hU h0
  rw [Mediation.condMean] at e1 e0
  rw [meanContrast, hU', e1, e0, sub_self]

/-- **Identification from strata if and only if the first stage matrix is injective.** With
strata `s` of a baseline variable `V` (any number), randomization within strata, the model at
`ψ₀` with reference time `T₀`, integrable times and both arms of positive probability in every
stratum, `ψ₀` is the only parameter vector satisfying all the stratum mean restrictions if and
only if the matrix of first stages, acting on the exponentiated parameters, is injective. -/
theorem identified_iff_injective {β : Type*} {μ : Measure Ω} [IsFiniteMeasure μ]
    (hR : Measurable M.R) {V : Ω → β} {T₀ : Ω → ℝ} {ψ₀ : ι → ℝ} (h : M.RefModel T₀ ψ₀)
    (hrand : M.toSwitchingTrial.RandomizedWithin μ V) (hU : Integrable M.U μ)
    (h₀ : Integrable T₀ μ) (hT : ∀ k, Integrable (M.Tk k) μ)
    (h1 : ∀ s, μ[|V ⁻¹' {s}] (M.R ⁻¹' {true}) ≠ 0)
    (h0 : ∀ s, μ[|V ⁻¹' {s}] (M.R ⁻¹' {false}) ≠ 0) :
    (∀ ψ : ι → ℝ, (∀ s, M.meanContrast μ[|V ⁻¹' {s}] (M.refCounterfactual T₀ ψ) = 0) →
        ψ = ψ₀) ↔ Function.Injective (M.firstStageMatrix μ V).mulVec := by
  have hv : ∀ s, μ (V ⁻¹' {s}) ≠ 0 := fun s ↦
    SwitchingTrial.stratum_ne_zero (M := M.toSwitchingTrial) (r := true) (h1 s)
  have e : ∀ ψ s, M.meanContrast μ[|V ⁻¹' {s}] (M.refCounterfactual T₀ ψ) =
      M.meanContrast μ[|V ⁻¹' {s}] T₀ + (M.firstStageMatrix μ V *ᵥ fun k ↦ Real.exp (ψ k)) s :=
    fun ψ s ↦ by
      rw [meanContrast_refCounterfactual (Mediation.integrable_cond_of_integrable h₀ (hv s))
        (fun k ↦ Mediation.integrable_cond_of_integrable (hT k) (hv s)) (h1 s) (h0 s)]
      simp only [Matrix.mulVec, dotProduct, firstStageMatrix]
      congr 1
      exact Finset.sum_congr rfl fun k _ ↦ mul_comm _ _
  have t : ∀ s, M.meanContrast μ[|V ⁻¹' {s}] (M.refCounterfactual T₀ ψ₀) = 0 := fun s ↦ by
    have := cond_isProbabilityMeasure (μ := μ) (hv s)
    exact meanContrast_refCounterfactual_trueParam hR h (hrand s (hv s))
      (Mediation.integrable_cond_of_integrable hU (hv s)) (h1 s) (h0 s)
  have key : ∀ ψ : ι → ℝ,
      (∀ s, M.meanContrast μ[|V ⁻¹' {s}] (M.refCounterfactual T₀ ψ) = 0) ↔
        (M.firstStageMatrix μ V *ᵥ fun k ↦ Real.exp (ψ k)) =
          M.firstStageMatrix μ V *ᵥ fun k ↦ Real.exp (ψ₀ k) := fun ψ ↦ by
    constructor
    · intro hs
      funext s
      have a := hs s
      have b := t s
      rw [e] at a b
      linarith
    · intro hF s
      have b := t s
      rw [e] at b ⊢
      rw [hF]
      exact b
  constructor
  · intro huniq a b hab
    suffices hker : ∀ v, M.firstStageMatrix μ V *ᵥ v = 0 → v = 0 from
      sub_eq_zero.1 (hker _ (by rw [Matrix.mulVec_sub, hab, sub_self]))
    intro v hv0
    have hev : ∀ᶠ τ in 𝓝 (0 : ℝ), ∀ k, 0 < Real.exp (ψ₀ k) + τ * v k := by
      refine eventually_all.2 fun k ↦ ?_
      have hc : Tendsto (fun τ : ℝ ↦ Real.exp (ψ₀ k) + τ * v k) (𝓝 0)
          (𝓝 (Real.exp (ψ₀ k))) := by
        have hcont : Continuous fun τ : ℝ ↦ Real.exp (ψ₀ k) + τ * v k := by fun_prop
        have := hcont.tendsto 0
        rwa [zero_mul, add_zero] at this
      exact hc.eventually (lt_mem_nhds (Real.exp_pos _))
    obtain ⟨τ, hτ, hτ0⟩ :=
      ((hev.filter_mono nhdsWithin_le_nhds).and (self_mem_nhdsWithin (s := {(0 : ℝ)}ᶜ))).exists
    have hτ0' : τ ≠ 0 := hτ0
    have hexp : (fun k ↦ Real.exp (Real.log (Real.exp (ψ₀ k) + τ * v k))) =
        (fun k ↦ Real.exp (ψ₀ k)) + τ • v := by
      funext k
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      exact Real.exp_log (hτ k)
    have hψ := huniq (fun k ↦ Real.log (Real.exp (ψ₀ k) + τ * v k)) ((key _).2 (by
      rw [hexp, Matrix.mulVec_add, Matrix.mulVec_smul, hv0, smul_zero, add_zero]))
    funext k
    have hk := congrArg (fun ψ : ι → ℝ ↦ Real.exp (ψ k)) hψ
    simp only [Real.exp_log (hτ k)] at hk
    have : τ * v k = 0 := by linarith
    exact (mul_eq_zero.1 this).resolve_left hτ0'
  · intro hinj ψ hs
    funext k
    exact Real.exp_injective (congrFun (hinj ((key ψ).1 hs)) k)

/-- **Two levels and two strata: identification if and only if the determinant is nonzero.** -/
theorem identified_iff_det_ne_zero {M : MultiLevelTrial Ω (Fin 2)} {μ : Measure Ω}
    [IsFiniteMeasure μ] (hR : Measurable M.R) {V : Ω → Fin 2} {T₀ : Ω → ℝ} {ψ₀ : Fin 2 → ℝ}
    (h : M.RefModel T₀ ψ₀) (hrand : M.toSwitchingTrial.RandomizedWithin μ V)
    (hU : Integrable M.U μ) (h₀ : Integrable T₀ μ) (hT : ∀ k, Integrable (M.Tk k) μ)
    (h1 : ∀ s, μ[|V ⁻¹' {s}] (M.R ⁻¹' {true}) ≠ 0)
    (h0 : ∀ s, μ[|V ⁻¹' {s}] (M.R ⁻¹' {false}) ≠ 0) :
    (∀ ψ : Fin 2 → ℝ, (∀ s, M.meanContrast μ[|V ⁻¹' {s}] (M.refCounterfactual T₀ ψ) = 0) →
        ψ = ψ₀) ↔
      M.firstStageMatrix μ V 0 0 * M.firstStageMatrix μ V 1 1 -
        M.firstStageMatrix μ V 0 1 * M.firstStageMatrix μ V 1 0 ≠ 0 := by
  rw [identified_iff_injective hR h hrand hU h₀ hT h1 h0, Matrix.mulVec_injective_iff_isUnit,
    Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero, Matrix.det_fin_two]

/-- **A singular matrix of first stages leaves the parameters unidentified**: there is another
parameter vector satisfying both stratum mean restrictions. -/
theorem not_identified_of_det_eq_zero {M : MultiLevelTrial Ω (Fin 2)} {μ : Measure Ω}
    [IsFiniteMeasure μ] (hR : Measurable M.R) {V : Ω → Fin 2} {T₀ : Ω → ℝ} {ψ₀ : Fin 2 → ℝ}
    (h : M.RefModel T₀ ψ₀) (hrand : M.toSwitchingTrial.RandomizedWithin μ V)
    (hU : Integrable M.U μ) (h₀ : Integrable T₀ μ) (hT : ∀ k, Integrable (M.Tk k) μ)
    (h1 : ∀ s, μ[|V ⁻¹' {s}] (M.R ⁻¹' {true}) ≠ 0)
    (h0 : ∀ s, μ[|V ⁻¹' {s}] (M.R ⁻¹' {false}) ≠ 0)
    (hdet : M.firstStageMatrix μ V 0 0 * M.firstStageMatrix μ V 1 1 -
        M.firstStageMatrix μ V 0 1 * M.firstStageMatrix μ V 1 0 = 0) :
    ∃ ψ : Fin 2 → ℝ, ψ ≠ ψ₀ ∧
      ∀ s, M.meanContrast μ[|V ⁻¹' {s}] (M.refCounterfactual T₀ ψ) = 0 := by
  have := (identified_iff_det_ne_zero hR h hrand hU h₀ hT h1 h0).not.2 (not_not.2 hdet)
  push Not at this
  obtain ⟨ψ, hs, hne⟩ := this
  exact ⟨ψ, hne, hs⟩

end MultiLevelTrial

/-! ### The distributional restriction does not identify several levels -/

namespace DistributionalExample

open Mediation.Counterexample RPSFTMCounterexample

/-- The levels of `RPSFTMCounterexample.TwoParam`: time off treatment, on treatment 1, on
treatment 2. The untreated time is the observed time, so the model holds at `ψ₀ = (0, 0, 0)`. -/
noncomputable def trial : MultiLevelTrial Ω₀ (Fin 3) where
  R ω := ω.1
  Tk := ![TwoParam.Tc, TwoParam.T₁, TwoParam.T₂]
  U := TwoParam.untreated 0 0

theorem model : trial.Model ![0, 0, 0] := fun ω ↦
  congrFun (MultiLevelTrial.twoParam_counterfactual 0 0) ω

theorem randomized : IndepFun trial.R trial.U μ₀ := TwoParam.not_identified.1

/-- Independence of the arm and a function gives equal arm laws of that function. -/
theorem armLaw_eq_of_indepFun {X : Ω₀ → ℝ} (h : IndepFun trial.R X μ₀) :
    (μ₀[|trial.R ⁻¹' {true}]).map X = (μ₀[|trial.R ⁻¹' {false}]).map X := by
  let N : SwitchingTrial Ω₀ := { R := trial.R, T := X, Te := X, U := X }
  have e1 := SwitchingTrial.armLaw_U_of_randomized (M := N) (μ := μ₀) (r := true)
    (measurable_of_finite _) (measurable_of_finite _) h (arm_ne_zero N (fun _ ↦ rfl) true)
  have e0 := SwitchingTrial.armLaw_U_of_randomized (M := N) (μ := μ₀) (r := false)
    (measurable_of_finite _) (measurable_of_finite _) h (arm_ne_zero N (fun _ ↦ rfl) false)
  exact e1.trans e0.symm

/-- **The full distributional restriction does not identify several levels.** The model holds
at `ψ₀ = (0, 0, 0)` with the arm independent of the untreated time, and at `ψ = (0, log 2, log 3)`
the candidate untreated time has the same law in the two arms, as it has at `ψ₀`. -/
theorem not_identified :
    trial.Model ![0, 0, 0] ∧ IndepFun trial.R trial.U μ₀ ∧
      (μ₀[|trial.R ⁻¹' {true}]).map (trial.counterfactual ![0, 0, 0]) =
        (μ₀[|trial.R ⁻¹' {false}]).map (trial.counterfactual ![0, 0, 0]) ∧
      (μ₀[|trial.R ⁻¹' {true}]).map (trial.counterfactual ![0, Real.log 2, Real.log 3]) =
        (μ₀[|trial.R ⁻¹' {false}]).map (trial.counterfactual ![0, Real.log 2, Real.log 3]) ∧
      (![0, Real.log 2, Real.log 3] : Fin 3 → ℝ) ≠ ![0, 0, 0] := by
  have c0 : trial.counterfactual ![0, 0, 0] = TwoParam.untreated 0 0 :=
    (MultiLevelTrial.twoParam_counterfactual 0 0).symm
  have c1 : trial.counterfactual ![0, Real.log 2, Real.log 3] =
      TwoParam.untreated (Real.log 2) (Real.log 3) :=
    (MultiLevelTrial.twoParam_counterfactual _ _).symm
  refine ⟨model, randomized, ?_, ?_, fun he ↦ ?_⟩
  · rw [c0]; exact armLaw_eq_of_indepFun TwoParam.not_identified.1
  · rw [c1]; exact armLaw_eq_of_indepFun TwoParam.not_identified.2.1
  · have := congrFun he 1
    simp only [Matrix.cons_val_one, Matrix.cons_val_zero] at this
    exact (Real.log_pos one_lt_two).ne' (by simpa using this)

end DistributionalExample

end StructuralNested

end CausalInference
