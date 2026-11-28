/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.Efficiency.ScoreSubmodel
public import CausalInference.Efficiency.InfluenceFunction
public import Mathlib.Analysis.Calculus.Deriv.Slope
public import Mathlib.Analysis.Calculus.ParametricIntegral

/-!
# Pathwise differentiability of the arm mean functional

The observed data functional of an arm is
`ψ(ν) = ∫ ν[1{T} Y | X] / ν[1{T} | X] dν`, the mean over the covariate of the regression of the
outcome on the covariate among the units with `T = 1` (`regressionFunctional`). For the arm `a`
of a point treatment, `T = 1{A = a}`, and under mean ignorability and positivity it equals
`E[Y(a)]` (`regressionFunctional_arm_eq`).

Along every score submodel `dμ_t = (1 + t S) dμ` with `S = s(O)` bounded, measurable and
centered, `t ↦ ψ(μ_t)` is differentiable at `0` with derivative `E[φ_a(O) s(O)]`, where `φ_a` is
the influence function `armEIF` of `CausalInference.Efficiency.InfluenceFunction`
(`hasDerivAt_regressionFunctional_arm`). In the language of semiparametric theory, `ψ` is
pathwise differentiable in the nonparametric model of the observed data with gradient `φ_a`.

## Main definitions

* `boolToReal`: the real indicator of a Boolean.
* `regressionFunctional ν T X Y`: the observed data functional.

## Main results

* `hasDerivAt_regressionFunctional`: the derivative along a score submodel, for a general
  indicator `T`, a version `e` of `P(T = 1 | X)` with `e ≥ ε > 0` and a version `m₁` with
  `E[1{T} Y | X] = e(X) m₁(X)`.
* `regressionFunctional_arm_eq`, `hasDerivAt_regressionFunctional_arm`: the arm of a point
  treatment.

## References

* J. Hahn, *On the role of the propensity score in efficient semiparametric estimation of
  average treatment effects*, Econometrica 66 (1998).
* A. W. van der Vaart, *Asymptotic Statistics*, Cambridge University Press (1998).
-/

@[expose] public section

namespace CausalInference
namespace Efficiency

open MeasureTheory ProbabilityTheory Filter Topology MissingData PointTreatment
open scoped ENNReal NNReal

/-- The real indicator of a Boolean: `1` for `true` and `0` for `false`. -/
def boolToReal (b : Bool) : ℝ := if b then 1 else 0

theorem respInd_eq_boolToReal {Ω : Type*} (A : Ω → Bool) (ω : Ω) :
    respInd A ω = boolToReal (A ω) := by
  rw [respInd_apply]; rfl

section Derivative

variable {Ω 𝒳 : Type*} [mΩ : MeasurableSpace Ω] [MeasurableSpace 𝒳]

theorem integrable_boolToReal {μ : Measure Ω} [IsFiniteMeasure μ] {T : Ω → Bool}
    (hT : Measurable T) : Integrable (fun ω ↦ boolToReal (T ω)) μ :=
  Integrable.of_bound ((Measurable.of_discrete (f := boolToReal)).comp hT).aestronglyMeasurable 1
    (Eventually.of_forall fun ω ↦ by cases T ω <;> simp [boolToReal])

/-- The **observed data functional** `ψ(ν) = ∫ ν[1{T} Y | X] / ν[1{T} | X] dν` of a law `ν` of
`(X, T, Y)`. It is used only at laws for which `ν[1{T} | X]` is bounded below by a positive
constant, so that the quotient is not a totalized value. -/
noncomputable def regressionFunctional (ν : Measure Ω) (T : Ω → Bool) (X : Ω → 𝒳) (Y : Ω → ℝ) :
    ℝ :=
  ∫ ω, ν[fun ω ↦ boolToReal (T ω) * Y ω | MeasurableSpace.comap X inferInstance] ω /
    ν[fun ω ↦ boolToReal (T ω) | MeasurableSpace.comap X inferInstance] ω ∂ν

variable {μ : Measure Ω} [IsProbabilityMeasure μ] {T : Ω → Bool} {X : Ω → 𝒳} {Y : Ω → ℝ}
  {e m₁ : 𝒳 → ℝ} {eps : ℝ}

/-- **The derivative of the observed data functional along a score submodel.** Let `e` be a
version of `P(T = 1 | X)` with `ε ≤ e(X) ≤ 1` almost surely, `ε > 0`, and let `m₁` satisfy
`E[1{T} Y | X] = e(X) m₁(X)` with `m₁(X)` integrable. For every bounded measurable `S` with
`E[S] = 0` and every constant `ψ`, `t ↦ ψ(μ_t)` along `dμ_t = (1 + t S) dμ` has derivative
`E[(1{T} (Y - m₁(X)) / e(X) + m₁(X) - ψ) S]` at `t = 0`. -/
theorem hasDerivAt_regressionFunctional (hT : Measurable T) (hX : Measurable X)
    (hY : Integrable Y μ) (he : Measurable e) (hm : Measurable m₁)
    (hps : μ[fun ω ↦ boolToReal (T ω) | MeasurableSpace.comap X inferInstance] =ᵐ[μ]
      fun ω ↦ e (X ω))
    (hnum : μ[fun ω ↦ boolToReal (T ω) * Y ω | MeasurableSpace.comap X inferInstance] =ᵐ[μ]
      fun ω ↦ e (X ω) * m₁ (X ω))
    (hMI : Integrable (fun ω ↦ m₁ (X ω)) μ) (heps : 0 < eps)
    (hE : ∀ᵐ ω ∂μ, eps ≤ e (X ω) ∧ e (X ω) ≤ 1) {S : Ω → ℝ} (hS : Measurable S) {C : ℝ}
    (hC : ∀ ω, |S ω| ≤ C) (hS0 : ∫ ω, S ω ∂μ = 0) (ψ : ℝ) :
    HasDerivAt (fun t ↦ regressionFunctional (scoreTilt μ S t) T X Y)
      (∫ ω, (boolToReal (T ω) * (Y ω - m₁ (X ω)) / e (X ω) + m₁ (X ω) - ψ) * S ω ∂μ) 0 := by
  have hm𝒢 : MeasurableSpace.comap X inferInstance ≤ mΩ := hX.comap_le
  set K : ℝ := |C| + 1 with hKdef
  have hK : 0 < K := by positivity
  have hK1 : 1 ≤ K := by simp only [hKdef]; linarith [abs_nonneg C]
  set δ : ℝ := (2 * K)⁻¹ with hδdef
  have hδ : 0 < δ := by positivity
  have hδK : δ * K = 1 / 2 := by rw [hδdef]; field_simp
  have hSm : Measurable S := hS
  have hSK : ∀ ω, |S ω| ≤ K := fun ω ↦ (hC _).trans (by linarith [le_abs_self C])
  set Tb : Ω → ℝ := fun ω ↦ boolToReal (T ω) with hTbdef
  have hTbm : Measurable Tb := (Measurable.of_discrete (f := boolToReal)).comp hT
  have hTb : ∀ ω, 0 ≤ Tb ω ∧ Tb ω ≤ 1 := fun ω ↦ by
    simp only [hTbdef]; cases T ω <;> simp [boolToReal]
  have hTbn : ∀ ω, ‖Tb ω‖ ≤ 1 := fun ω ↦ by
    rw [Real.norm_of_nonneg (hTb ω).1]; exact (hTb ω).2
  have hSn : ∀ ω, ‖S ω‖ ≤ K := fun ω ↦ by rw [Real.norm_eq_abs]; exact hSK ω
  -- integrability
  have hSI : Integrable S μ :=
    Integrable.of_bound hSm.aestronglyMeasurable K (Eventually.of_forall hSn)
  have hTbI : Integrable Tb μ := integrable_boolToReal hT
  have hTY : Integrable (fun ω ↦ Tb ω * Y ω) μ := by
    have := hY.mul_bdd hTbm.aestronglyMeasurable (c := 1) (Eventually.of_forall hTbn)
    exact this.congr (Eventually.of_forall fun ω ↦ by simp only [mul_comm])
  have hSTY : Integrable (fun ω ↦ S ω * (Tb ω * Y ω)) μ := by
    have := hTY.mul_bdd hSm.aestronglyMeasurable (c := K) (Eventually.of_forall hSn)
    exact this.congr (Eventually.of_forall fun ω ↦ by simp only [mul_comm])
  have hSTb : Integrable (fun ω ↦ S ω * Tb ω) μ := by
    have := hTbI.mul_bdd hSm.aestronglyMeasurable (c := K) (Eventually.of_forall hSn)
    exact this.congr (Eventually.of_forall fun ω ↦ by simp only [mul_comm])
  have hS1 : Integrable (fun ω ↦ S ω * 1) μ := hSI.congr (Eventually.of_forall fun ω ↦ by simp)
  -- the conditional means of the score terms
  set a : Ω → ℝ := μ[S | MeasurableSpace.comap X inferInstance] with hadef
  set b : Ω → ℝ := μ[fun ω ↦ S ω * (Tb ω * Y ω) | MeasurableSpace.comap X inferInstance]
    with hbdef
  set c : Ω → ℝ := μ[fun ω ↦ S ω * Tb ω | MeasurableSpace.comap X inferInstance] with hcdef
  set E : Ω → ℝ := fun ω ↦ e (X ω) with hEdef
  set M : Ω → ℝ := fun ω ↦ m₁ (X ω) with hMdef
  have ham : Measurable a := (stronglyMeasurable_condExp.mono hm𝒢).measurable
  have hbm : Measurable b := (stronglyMeasurable_condExp.mono hm𝒢).measurable
  have hcm : Measurable c := (stronglyMeasurable_condExp.mono hm𝒢).measurable
  have hEm : Measurable E := he.comp hX
  have hMm : Measurable M := hm.comp hX
  have hEg : Measurable[MeasurableSpace.comap X inferInstance] E :=
    he.comp (comap_measurable X)
  have hMg : Measurable[MeasurableSpace.comap X inferInstance] M :=
    hm.comp (comap_measurable X)
  have hbI : Integrable b μ := integrable_condExp
  have hkTb : ∀ k : ℝ, μ[fun ω ↦ k * Tb ω | MeasurableSpace.comap X inferInstance] =ᵐ[μ]
      fun ω ↦ k * E ω := fun k ↦ by
    filter_upwards [condExp_smul (μ := μ) k Tb (MeasurableSpace.comap X inferInstance), hps]
      with ω h1 h2
    exact h1.trans (by rw [Pi.smul_apply, smul_eq_mul, ← h2])
  have ha : ∀ᵐ ω ∂μ, |a ω| ≤ K := by
    have hu := condExp_mono (m := MeasurableSpace.comap X inferInstance) hSI
      (integrable_const K) (Eventually.of_forall fun ω ↦ (abs_le.mp (hSK ω)).2)
    have hl := condExp_mono (m := MeasurableSpace.comap X inferInstance)
      (integrable_const (-K)) hSI (Eventually.of_forall fun ω ↦ (abs_le.mp (hSK ω)).1)
    rw [condExp_const hm𝒢] at hu hl
    filter_upwards [hu, hl] with ω h1 h2
    exact abs_le.mpr ⟨h2, h1⟩
  have hc : ∀ᵐ ω ∂μ, |c ω| ≤ K * E ω := by
    have hkI : ∀ k : ℝ, Integrable (fun ω ↦ k * Tb ω) μ := fun k ↦ hTbI.const_mul k
    have hu := condExp_mono (m := MeasurableSpace.comap X inferInstance) hSTb (hkI K)
      (Eventually.of_forall fun ω ↦ by
        nlinarith [(abs_le.mp (hSK ω)).2, (hTb ω).1])
    have hl := condExp_mono (m := MeasurableSpace.comap X inferInstance) (hkI (-K)) hSTb
      (Eventually.of_forall fun ω ↦ by
        nlinarith [(abs_le.mp (hSK ω)).1, (hTb ω).1])
    filter_upwards [hu, hl, hkTb K, hkTb (-K)] with ω h1 h2 h3 h4
    rw [h3] at h1
    rw [h4] at h2
    exact abs_le.mpr ⟨by linarith, h1⟩
  -- the g-formula along the submodel
  set G : ℝ → Ω → ℝ := fun t ω ↦ (1 + t * a ω) * (E ω * M ω + t * b ω) / (E ω + t * c ω)
    with hGdef
  set Q : ℝ → Ω → ℝ := fun t ω ↦
    (b ω + a ω * E ω * M ω - M ω * c ω + t * a ω * b ω) / (E ω + t * c ω) with hQdef
  set bound : Ω → ℝ := fun ω ↦ (2 * |b ω| + 2 * K * |M ω|) / (eps / 2) with hbounddef
  have hboundI : Integrable bound μ :=
    ((hbI.abs.const_mul 2).add (hMI.abs.const_mul (2 * K))).div_const _
  have hQm : ∀ t, Measurable (Q t) := fun t ↦
    ((((hbm.add ((ham.mul hEm).mul hMm)).sub (hMm.mul hcm)).add
      ((_root_.measurable_const.mul ham).mul hbm))).div (hEm.add (_root_.measurable_const.mul hcm))
  have hQb : ∀ t, |t| < δ → ∀ᵐ ω ∂μ, E ω / 2 ≤ E ω + t * c ω ∧ ‖Q t ω‖ ≤ bound ω := by
    intro t ht
    have htK : |t| * K ≤ 1 / 2 := by
      rw [← hδK]; exact mul_le_mul_of_nonneg_right ht.le hK.le
    filter_upwards [ha, hc, hE] with ω h1 h2 h3
    rw [Real.norm_eq_abs]
    exact abs_tilt_quotient_le hK heps h1 h2 h3.1 h3.2 htK
  have hQI : ∀ t, |t| < δ → Integrable (Q t) μ := fun t ht ↦
    Integrable.mono' hboundI (hQm t).aestronglyMeasurable ((hQb t ht).mono fun _ h ↦ h.2)
  have hψ : ∀ t, |t| < δ → regressionFunctional (scoreTilt μ S t) T X Y =
      ∫ ω, M ω ∂μ + t * ∫ ω, Q t ω ∂μ := by
    intro t ht
    have htK : |t| * K ≤ 1 / 2 := by
      rw [← hδK]; exact mul_le_mul_of_nonneg_right ht.le hK.le
    have ht1 : |t| ≤ 1 / 2 := by nlinarith [abs_nonneg t, hK1]
    set ρ : Ω → ℝ := fun ω ↦ 1 + t * S ω with hρdef
    have hρm : Measurable ρ := _root_.measurable_const.add (_root_.measurable_const.mul hSm)
    have htS : ∀ ω, |t * S ω| ≤ 1 / 2 := fun ω ↦ by
      rw [abs_mul]
      exact (mul_le_mul_of_nonneg_left (hSK ω) (abs_nonneg t)).trans htK
    have hρl : ∀ ω, 1 / 2 ≤ ρ ω := fun ω ↦ by
      simp only [hρdef]; linarith [neg_abs_le (t * S ω), htS ω]
    have hρu : ∀ ω, ρ ω ≤ 3 / 2 := fun ω ↦ by
      simp only [hρdef]; linarith [le_abs_self (t * S ω), htS ω]
    have hρ0 : ∀ ω, 0 ≤ ρ ω := fun ω ↦ by linarith [hρl ω]
    have hρI : Integrable ρ μ := (integrable_const 1).add (hSI.const_mul t)
    have hsub : scoreTilt μ S t =
        μ.withDensity fun ω ↦ ENNReal.ofReal (ρ ω) := rfl
    have hN := condExp_withDensity_ofReal_ae_eq hX hρm (by norm_num : (0 : ℝ) < 1 / 2) hρl hρu hTY
    have hD := condExp_withDensity_ofReal_ae_eq hX hρm (by norm_num : (0 : ℝ) < 1 / 2) hρl hρu hTbI
    have hW : μ[ρ | MeasurableSpace.comap X inferInstance] =ᵐ[μ] fun ω ↦ 1 + t * a ω := by
      have h := condExp_one_add_mul_ae_eq (μ := μ) (MeasurableSpace.comap X inferInstance)
        (integrable_const (1 : ℝ)) hS1 t
      rw [condExp_const hm𝒢] at h
      have e1 : (fun ω ↦ (1 + t * S ω) * 1) = ρ := by funext ω; simp [hρdef]
      have e2 : (fun ω ↦ S ω * 1) = S := by funext ω; simp
      rw [e1, e2] at h
      exact h
    have hWl : ∀ᵐ ω ∂μ, 1 / 2 ≤ μ[ρ | MeasurableSpace.comap X inferInstance] ω := by
      have h := condExp_mono (m := MeasurableSpace.comap X inferInstance)
        (integrable_const (1 / 2 : ℝ)) hρI (Eventually.of_forall hρl)
      rw [condExp_const hm𝒢] at h
      exact h
    have hNt : μ[ρ * fun ω ↦ Tb ω * Y ω | MeasurableSpace.comap X inferInstance] =ᵐ[μ]
        fun ω ↦ E ω * M ω + t * b ω := by
      have h := condExp_one_add_mul_ae_eq (μ := μ) (MeasurableSpace.comap X inferInstance) hTY
        hSTY t
      filter_upwards [h, hnum] with ω h1 h2
      exact h1.trans (by rw [h2])
    have hDt : μ[ρ * Tb | MeasurableSpace.comap X inferInstance] =ᵐ[μ]
        fun ω ↦ E ω + t * c ω := by
      have h := condExp_one_add_mul_ae_eq (μ := μ) (MeasurableSpace.comap X inferInstance) hTbI
        hSTb t
      filter_upwards [h, hps] with ω h1 h2
      exact h1.trans (by rw [← h2])
    set q : Ω → ℝ := μ[ρ * fun ω ↦ Tb ω * Y ω | MeasurableSpace.comap X inferInstance] /
      μ[ρ * Tb | MeasurableSpace.comap X inferInstance] with hqdef
    have hqg : StronglyMeasurable[MeasurableSpace.comap X inferInstance] q :=
      stronglyMeasurable_condExp.div stronglyMeasurable_condExp
    have hqe : q =ᵐ[μ] fun ω ↦ (E ω * M ω + t * b ω) / (E ω + t * c ω) := by
      filter_upwards [hNt, hDt] with ω h1 h2
      simp only [hqdef, Pi.div_apply, h1, h2]
    have hqI : Integrable q μ := by
      refine Integrable.mono' ((hMI.abs.add hbI.abs).mul_const (2 / eps))
        (hqg.mono hm𝒢).aestronglyMeasurable ?_
      filter_upwards [hqe, hQb t ht, hE] with ω h1 h2 h3
      rw [h1, Real.norm_eq_abs, abs_div]
      have hd : eps / 2 ≤ |E ω + t * c ω| := by
        rw [abs_of_pos (by linarith [h2.1, h3.1])]; linarith [h2.1, h3.1]
      have hn : |E ω * M ω + t * b ω| ≤ |M ω| + |b ω| := by
        calc |E ω * M ω + t * b ω| ≤ |E ω * M ω| + |t * b ω| := abs_add_le _ _
          _ ≤ |M ω| + |b ω| := by
            rw [abs_mul, abs_mul, abs_of_nonneg (heps.le.trans h3.1)]
            gcongr
            · nlinarith [abs_nonneg (M ω), h3.2]
            · nlinarith [abs_nonneg (b ω)]
      calc |E ω * M ω + t * b ω| / |E ω + t * c ω| ≤ (|M ω| + |b ω|) / (eps / 2) :=
            div_le_div₀ (by positivity) hn (by positivity) hd
        _ = (|M ω| + |b ω|) * (2 / eps) := by field_simp
    have hρq : Integrable (ρ * q) μ := by
      have := hqI.mul_bdd hρm.aestronglyMeasurable (c := 3 / 2) (Eventually.of_forall fun ω ↦ by
        rw [Real.norm_of_nonneg (hρ0 ω)]; exact hρu ω)
      exact this.congr (Eventually.of_forall fun ω ↦ by simp only [Pi.mul_apply, mul_comm])
    have hνμ : scoreTilt μ S t ≪ μ := by
      rw [hsub]; exact withDensity_absolutelyContinuous _ _
    calc regressionFunctional (scoreTilt μ S t) T X Y
        = ∫ ω, q ω ∂(μ.withDensity fun ω ↦ ENNReal.ofReal (ρ ω)) := by
          rw [regressionFunctional, hsub]
          refine integral_congr_ae (withDensity_absolutelyContinuous _ _ ?_)
          filter_upwards [hN, hD, hWl] with ω h1 h2 h3
          rw [h1, h2, Pi.div_apply, Pi.div_apply]
          simp only [hqdef, Pi.div_apply]
          exact div_div_div_cancel_right₀ (by linarith) _ _
      _ = ∫ ω, ρ ω * q ω ∂μ := integral_withDensity_ofReal_eq hρm hρ0 q
      _ = ∫ ω, μ[ρ | MeasurableSpace.comap X inferInstance] ω * q ω ∂μ :=
          integral_mul_eq_integral_condExp_mul hm𝒢 hqg hρI hρq
      _ = ∫ ω, (M ω + t * Q t ω) ∂μ := by
          refine integral_congr_ae ?_
          filter_upwards [hW, hqe, hQb t ht, hE] with ω h1 h2 h3 h4
          have hE0 : E ω ≠ 0 := (heps.trans_le h4.1).ne'
          have hd0 : E ω + t * c ω ≠ 0 := by linarith [h3.1, heps.trans_le h4.1]
          rw [h1, h2]
          simp only [hQdef]
          field_simp
          ring
      _ = ∫ ω, M ω ∂μ + t * ∫ ω, Q t ω ∂μ := by
          rw [integral_add hMI ((hQI t ht).const_mul t), integral_const_mul]
  -- the derivative
  have hcont : ContinuousAt (fun t ↦ ∫ ω, Q t ω ∂μ) 0 := by
    refine continuousAt_of_dominated (bound := bound)
      (Eventually.of_forall fun t ↦ (hQm t).aestronglyMeasurable) ?_ hboundI ?_
    · filter_upwards [Metric.ball_mem_nhds (0 : ℝ) hδ] with t ht
      have ht' : |t| < δ := by simpa [Metric.mem_ball, Real.dist_eq] using ht
      exact (hQb t ht').mono fun _ h ↦ h.2
    · filter_upwards [hE] with ω h
      have hE0 : E ω ≠ 0 := (heps.trans_le h.1).ne'
      refine ContinuousAt.div (by fun_prop) (by fun_prop) ?_
      simpa using hE0
  have hlim : Tendsto (fun t ↦ ∫ ω, Q t ω ∂μ) (𝓝[≠] 0) (𝓝 (∫ ω, Q 0 ω ∂μ)) :=
    hcont.tendsto.mono_left nhdsWithin_le_nhds
  have hψ0 := hψ 0 (by simpa using hδ)
  rw [zero_mul, add_zero] at hψ0
  have hval : ∫ ω, Q 0 ω ∂μ =
      ∫ ω, (boolToReal (T ω) * (Y ω - m₁ (X ω)) / e (X ω) + m₁ (X ω) - ψ) * S ω ∂μ := by
    have hEinv : ∀ᵐ ω ∂μ, ‖(E ω)⁻¹‖ ≤ eps⁻¹ := hE.mono fun ω h ↦ by
      rw [norm_inv, Real.norm_of_nonneg (heps.le.trans h.1)]
      exact inv_anti₀ heps h.1
    have hEinvm : Measurable fun ω ↦ (E ω)⁻¹ := hEm.inv
    have hEinvg : StronglyMeasurable[MeasurableSpace.comap X inferInstance]
        fun ω ↦ (E ω)⁻¹ := hEg.inv.stronglyMeasurable
    have hMEg : StronglyMeasurable[MeasurableSpace.comap X inferInstance]
        fun ω ↦ M ω * (E ω)⁻¹ := (hMg.mul hEg.inv).stronglyMeasurable
    have hMEI : Integrable (fun ω ↦ M ω * (E ω)⁻¹) μ :=
      hMI.mul_bdd hEinvm.aestronglyMeasurable hEinv
    have hcK : ∀ᵐ ω ∂μ, ‖c ω‖ ≤ K := by
      filter_upwards [hc, hE] with ω h1 h2
      rw [Real.norm_eq_abs]
      nlinarith [h2.2]
    have haK : ∀ᵐ ω ∂μ, ‖a ω‖ ≤ K := ha.mono fun ω h ↦ by rwa [Real.norm_eq_abs]
    have hSTbn : ∀ ω, ‖S ω * Tb ω‖ ≤ K := fun ω ↦ by
      rw [norm_mul]
      nlinarith [hSn ω, hTbn ω, norm_nonneg (S ω), norm_nonneg (Tb ω)]
    have I1 : Integrable (fun ω ↦ b ω * (E ω)⁻¹) μ :=
      hbI.mul_bdd hEinvm.aestronglyMeasurable hEinv
    have I2 : Integrable (fun ω ↦ c ω * (M ω * (E ω)⁻¹)) μ :=
      (hMEI.mul_bdd hcm.aestronglyMeasurable hcK).congr
        (Eventually.of_forall fun ω ↦ by ring)
    have I3 : Integrable (fun ω ↦ a ω * M ω) μ :=
      (hMI.mul_bdd ham.aestronglyMeasurable haK).congr
        (Eventually.of_forall fun ω ↦ by ring)
    have J1 : Integrable (fun ω ↦ S ω * (Tb ω * Y ω) * (E ω)⁻¹) μ :=
      hSTY.mul_bdd hEinvm.aestronglyMeasurable hEinv
    have J2 : Integrable (fun ω ↦ S ω * Tb ω * (M ω * (E ω)⁻¹)) μ :=
      (hMEI.mul_bdd (hSm.mul hTbm).aestronglyMeasurable (c := K)
        (Eventually.of_forall hSTbn)).congr
        (Eventually.of_forall fun ω ↦ by simp only [Pi.mul_apply]; ring)
    have J3 : Integrable (fun ω ↦ S ω * M ω) μ :=
      hMI.mul_bdd hSm.aestronglyMeasurable (c := K) (Eventually.of_forall hSn) |>.congr
        (Eventually.of_forall fun ω ↦ by ring)
    have P1 : ∫ ω, S ω * (Tb ω * Y ω) * (E ω)⁻¹ ∂μ = ∫ ω, b ω * (E ω)⁻¹ ∂μ :=
      integral_mul_eq_integral_condExp_mul hm𝒢 hEinvg hSTY J1
    have P2 : ∫ ω, S ω * Tb ω * (M ω * (E ω)⁻¹) ∂μ = ∫ ω, c ω * (M ω * (E ω)⁻¹) ∂μ :=
      integral_mul_eq_integral_condExp_mul hm𝒢 hMEg hSTb J2
    have P3 : ∫ ω, S ω * M ω ∂μ = ∫ ω, a ω * M ω ∂μ :=
      integral_mul_eq_integral_condExp_mul hm𝒢 hMg.stronglyMeasurable hSI J3
    have hφ : ∫ ω, (boolToReal (T ω) * (Y ω - m₁ (X ω)) / e (X ω) + m₁ (X ω) - ψ) * S ω ∂μ =
        ∫ ω, S ω * (Tb ω * Y ω) * (E ω)⁻¹ ∂μ - ∫ ω, S ω * Tb ω * (M ω * (E ω)⁻¹) ∂μ +
          ∫ ω, S ω * M ω ∂μ - ψ * ∫ ω, S ω ∂μ := by
      have J12 : Integrable (fun ω ↦ S ω * (Tb ω * Y ω) * (E ω)⁻¹ -
          S ω * Tb ω * (M ω * (E ω)⁻¹)) μ := J1.sub J2
      have J123 : Integrable (fun ω ↦ S ω * (Tb ω * Y ω) * (E ω)⁻¹ -
          S ω * Tb ω * (M ω * (E ω)⁻¹) + S ω * M ω) μ := J12.add J3
      have J4 : Integrable (fun ω ↦ ψ * S ω) μ := hSI.const_mul _
      rw [← integral_sub J1 J2, ← integral_add J12 J3, ← integral_const_mul,
        ← integral_sub J123 J4]
      refine integral_congr_ae (Eventually.of_forall fun ω ↦ ?_)
      simp only [hTbdef, hEdef, hMdef]
      ring
    have hQ0 : ∫ ω, Q 0 ω ∂μ = ∫ ω, b ω * (E ω)⁻¹ ∂μ - ∫ ω, c ω * (M ω * (E ω)⁻¹) ∂μ +
        ∫ ω, a ω * M ω ∂μ := by
      have I12 : Integrable (fun ω ↦ b ω * (E ω)⁻¹ - c ω * (M ω * (E ω)⁻¹)) μ := I1.sub I2
      rw [← integral_sub I1 I2, ← integral_add I12 I3]
      refine integral_congr_ae ?_
      filter_upwards [hE] with ω h
      have hE0 : E ω ≠ 0 := (heps.trans_le h.1).ne'
      simp only [hQdef, zero_mul, add_zero]
      field_simp
      ring
    rw [hφ, hQ0, P1, P2, P3, hS0, mul_zero, sub_zero]
  rw [hasDerivAt_iff_tendsto_slope_zero, ← hval]
  refine hlim.congr' ?_
  filter_upwards [nhdsWithin_le_nhds (Metric.ball_mem_nhds (0 : ℝ) hδ),
    self_mem_nhdsWithin] with t ht htne
  have ht' : |t| < δ := by simpa [Metric.mem_ball, Real.dist_eq] using ht
  have htne' : t ≠ 0 := htne
  rw [zero_add, hψ t ht', hψ0, smul_eq_mul, add_sub_cancel_left]
  field_simp

end Derivative

section Arm

variable {Ω 𝒲 : Type*} {mΩ : MeasurableSpace Ω} [MeasurableSpace 𝒲]
  {A : Ω → Bool} {Y : Bool → Ω → ℝ} {W : Ω → 𝒲} {e : 𝒲 → ℝ} {m : Bool → 𝒲 → ℝ}
  {μ : Measure Ω} [IsProbabilityMeasure μ]

theorem condExp_arm_boolToReal (hW : Measurable W) (hA : Measurable A)
    (hps : IsPropensityScore μ A W e) (a : Bool) :
    μ[fun ω ↦ boolToReal (arm A a ω) | MeasurableSpace.comap W inferInstance] =ᵐ[μ]
      fun ω ↦ armProb e a (W ω) := by
  have h : (fun ω ↦ boolToReal (arm A a ω)) = respInd (arm A a) :=
    funext fun ω ↦ (respInd_eq_boolToReal _ ω).symm
  rw [h]
  exact hps.condExp_arm hW hA a

/-- The numerator of the observed data functional of the arm `a`:
`E[1{A = a} Y | W] = π_a(W) m(a, W)` almost surely, for a correct regression `m` with `m(a, W)`
integrable. -/
theorem condExp_arm_mul_obsOutcome (hW : Measurable W) (hA : Measurable A)
    (hYo : Integrable (obsOutcome A Y) μ) (hps : IsPropensityScore μ A W e)
    (hreg : IsOutcomeRegression μ A W (obsOutcome A Y) m) (a : Bool)
    (hma : Integrable (fun ω ↦ m a (W ω)) μ) :
    μ[fun ω ↦ boolToReal (arm A a ω) * obsOutcome A Y ω |
        MeasurableSpace.comap W inferInstance] =ᵐ[μ]
      fun ω ↦ armProb e a (W ω) * m a (W ω) := by
  have hWA : (MeasurableSpace.comap (fun ω ↦ (W ω, A ω)) inferInstance) ≤ mΩ :=
    (hW.prodMk hA).comap_le
  have hle : MeasurableSpace.comap W inferInstance ≤
      (MeasurableSpace.comap (fun ω ↦ (W ω, A ω)) inferInstance) :=
    (measurable_fst.comp (comap_measurable fun ω ↦ (W ω, A ω))).comap_le
  have hb : ∀ ω, ‖boolToReal (arm A a ω)‖ ≤ 1 := fun ω ↦ by
    cases arm A a ω <;> simp [boolToReal]
  have hbm : Measurable fun ω ↦ boolToReal (arm A a ω) :=
    (Measurable.of_discrete (f := boolToReal)).comp (measurable_arm hA a)
  have hbWA : StronglyMeasurable[(MeasurableSpace.comap (fun ω ↦ (W ω, A ω)) inferInstance)]
      fun ω ↦ boolToReal (arm A a ω) := by
    have : (fun ω ↦ boolToReal (arm A a ω)) =
        (fun p : 𝒲 × Bool ↦ boolToReal (p.2 == a)) ∘ fun ω ↦ (W ω, A ω) := rfl
    rw [this]
    exact (((Measurable.of_discrete (f := fun b : Bool ↦ boolToReal (b == a))).comp
      measurable_snd).comp (comap_measurable fun ω ↦ (W ω, A ω))).stronglyMeasurable
  have hbY : Integrable (fun ω ↦ boolToReal (arm A a ω) * obsOutcome A Y ω) μ :=
    hYo.bdd_mul hbm.aestronglyMeasurable (Eventually.of_forall hb)
  have hbM : Integrable (fun ω ↦ boolToReal (arm A a ω) * m a (W ω)) μ :=
    hma.bdd_mul hbm.aestronglyMeasurable (Eventually.of_forall hb)
  have hinner : μ[fun ω ↦ boolToReal (arm A a ω) * obsOutcome A Y ω |
      (MeasurableSpace.comap (fun ω ↦ (W ω, A ω)) inferInstance)] =ᵐ[μ]
      fun ω ↦ boolToReal (arm A a ω) * m a (W ω) := by
    have h := condExp_mul_of_stronglyMeasurable_left
      (m := (MeasurableSpace.comap (fun ω ↦ (W ω, A ω)) inferInstance)) (μ := μ) hbWA hbY hYo
    filter_upwards [h, hreg.2] with ω h1 h2
    refine h1.trans ?_
    rw [Pi.mul_apply, h2]
    by_cases hω : A ω = a
    · rw [hω]
    · have : arm A a ω = false := by simp [arm, hω]
      simp [this, boolToReal]
  have hMW : StronglyMeasurable[MeasurableSpace.comap W inferInstance] fun ω ↦ m a (W ω) :=
    ((hreg.1 a).comp (comap_measurable W)).stronglyMeasurable
  have hout := condExp_mul_of_stronglyMeasurable_right (m := MeasurableSpace.comap W inferInstance)
    (μ := μ) (f := fun ω ↦ boolToReal (arm A a ω)) hMW hbM
    (integrable_boolToReal (measurable_arm hA a))
  calc μ[fun ω ↦ boolToReal (arm A a ω) * obsOutcome A Y ω |
        MeasurableSpace.comap W inferInstance]
      =ᵐ[μ] μ[μ[fun ω ↦ boolToReal (arm A a ω) * obsOutcome A Y ω |
          (MeasurableSpace.comap (fun ω ↦ (W ω, A ω)) inferInstance)] |
        MeasurableSpace.comap W inferInstance] := (condExp_condExp_of_le hle hWA).symm
    _ =ᵐ[μ] μ[fun ω ↦ boolToReal (arm A a ω) * m a (W ω) |
        MeasurableSpace.comap W inferInstance] := condExp_congr_ae hinner
    _ =ᵐ[μ] _ := by
        filter_upwards [hout, condExp_arm_boolToReal hW hA hps a] with ω h1 h2
        exact h1.trans (by rw [Pi.mul_apply, h2, mul_comm])

/-- **The observed data functional of an arm identifies its mean**: under mean ignorability of
the arm, a correct score and regression, and `π_a(W) ≥ ε > 0`,
`ψ(μ) = ∫ μ[1{A = a} Y | W] / μ[1{A = a} | W] dμ = E[Y(a)]`. -/
theorem regressionFunctional_arm_eq (hW : Measurable W) (hA : Measurable A)
    (hYi : ∀ a, Integrable (Y a) μ) (hps : IsPropensityScore μ A W e)
    (hreg : IsOutcomeRegression μ A W (obsOutcome A Y) m) (a : Bool)
    (hmi : MeanIgnorable μ A W Y a) {ε : ℝ} (hε : 0 < ε)
    (hpos : ∀ᵐ ω ∂μ, ε ≤ armProb e a (W ω)) :
    regressionFunctional μ (arm A a) W (obsOutcome A Y) = armMean μ Y a := by
  have hpos' : ∀ᵐ ω ∂μ, 0 < armProb e a (W ω) := hpos.mono fun _ h ↦ hε.trans_le h
  have hid := hreg.ae_eq_condExp hW hA hYi hps a hmi hpos'
  have hma : Integrable (fun ω ↦ m a (W ω)) μ := integrable_condExp.congr hid.symm
  have hN := condExp_arm_mul_obsOutcome hW hA (integrable_obsOutcome hA hYi) hps hreg a hma
  rw [armMean_eq_integral_regression hW hA hYi hreg hps a hmi hpos', regressionFunctional]
  refine integral_congr_ae ?_
  filter_upwards [hN, condExp_arm_boolToReal hW hA hps a, hpos'] with ω h1 h2 h3
  rw [h1, h2]
  field_simp [h3.ne']

/-- **Pathwise differentiability of the arm mean with gradient `φ_a`.** Under mean ignorability
of the arm, a correct score `e` and regression `m`, integrable potential outcomes and
`π_a(W) ≥ ε > 0`, for every bounded measurable score `s` of the observed data `O = (W, A, Y)`
with `E[s(O)] = 0`, the observed data functional along `dμ_t = (1 + t s(O)) dμ` is
differentiable at `t = 0` with derivative `E[φ_a(O) s(O)]`, `φ_a = armEIF e m a E[Y(a)]`. -/
theorem hasDerivAt_regressionFunctional_arm (hW : Measurable W) (hA : Measurable A)
    (hY : ∀ a, Measurable (Y a)) (hYi : ∀ a, Integrable (Y a) μ)
    (hps : IsPropensityScore μ A W e) (hreg : IsOutcomeRegression μ A W (obsOutcome A Y) m)
    (a : Bool) (hmi : MeanIgnorable μ A W Y a) {ε : ℝ} (hε : 0 < ε)
    (hpos : ∀ᵐ ω ∂μ, ε ≤ armProb e a (W ω)) {s : 𝒲 × Bool × ℝ → ℝ} (hs : Measurable s)
    {C : ℝ} (hC : ∀ z, |s z| ≤ C) (hs0 : ∫ ω, s (obsData A Y W ω) ∂μ = 0) :
    HasDerivAt (fun t ↦ regressionFunctional (scoreTilt μ (fun ω ↦ s (obsData A Y W ω)) t)
        (arm A a) W (obsOutcome A Y))
      (∫ ω, armEIF e m a (armMean μ Y a) (obsData A Y W ω) * s (obsData A Y W ω) ∂μ) 0 := by
  have hpos' : ∀ᵐ ω ∂μ, 0 < armProb e a (W ω) := hpos.mono fun _ h ↦ hε.trans_le h
  have hid := hreg.ae_eq_condExp hW hA hYi hps a hmi hpos'
  have hma : Integrable (fun ω ↦ m a (W ω)) μ := integrable_condExp.congr hid.symm
  have hE : ∀ᵐ ω ∂μ, ε ≤ armProb e a (W ω) ∧ armProb e a (W ω) ≤ 1 := by
    filter_upwards [hpos, hps.ae_mem_Icc hW hA] with ω h1 h2
    refine ⟨h1, ?_⟩
    cases a <;> simp only [armProb_true, armProb_false] <;> linarith [h2.1, h2.2]
  have h := hasDerivAt_regressionFunctional (measurable_arm hA a) hW
    (integrable_obsOutcome hA hYi) (measurable_armProb hps.1 a) (hreg.1 a)
    (condExp_arm_boolToReal hW hA hps a)
    (condExp_arm_mul_obsOutcome hW hA (integrable_obsOutcome hA hYi) hps hreg a hma) hma hε hE
    (hs.comp (measurable_obsData hW hA hY)) (fun ω ↦ hC _) hs0 (armMean μ Y a)
  convert h using 1
  · rfl
  refine integral_congr_ae (μ := μ)
    (f := fun ω ↦ armEIF e m a (armMean μ Y a) (obsData A Y W ω) * s (obsData A Y W ω))
    (hpos'.mono fun ω hω ↦ ?_)
  dsimp only [Function.comp_apply]
  rw [armEIF_obsData_eq a _ hω.ne']
  simp only [weightedResidual, respInd_eq_boolToReal]
  ring

end Arm

end Efficiency
end CausalInference
