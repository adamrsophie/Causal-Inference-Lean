/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import Mathlib.Probability.ConditionalExpectation
public import Mathlib.MeasureTheory.Measure.WithDensity
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut

/-!
# Score submodels: tilting a law by a bounded score

For a bounded measurable score `S` on `Ω` with `E[S] = 0`, the tilted measures
`dμ_t = (1 + t S) dμ` form a one dimensional submodel through `μ` with score `S` at `t = 0`.
When `S = s(O)` is a function of the observed data, these submodels span the tangent space of the
nonparametric model of the observed data. This file proves that the tilt is a probability measure
for `|t| sup |S| ≤ 1`, expresses conditional expectations under a tilted law through conditional
expectations under `μ`, and records the real bounds used for the dominated limits of the pathwise
derivative.

## Main definitions

* `scoreTilt μ S t`: the measure `(1 + t S) μ`.

## Main results

* `isProbabilityMeasure_scoreTilt`: the tilt is a probability measure.
* `condExp_withDensity_ofReal_ae_eq`: `ν[f | X] = μ[ρ f | X] / μ[ρ | X]` for `ν = ρ μ` with a
  density bounded away from `0` and `∞`.
* `abs_tilt_quotient_le`: the bound on the difference quotient.

## References

* A. W. van der Vaart, *Asymptotic Statistics*, Cambridge University Press (1998).
* P. J. Bickel, C. A. J. Klaassen, Y. Ritov and J. A. Wellner, *Efficient and Adaptive
  Estimation for Semiparametric Models*, Johns Hopkins University Press (1993).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace CausalInference
namespace Efficiency


section Tilt

variable {Ω : Type*} [mΩ : MeasurableSpace Ω]

/-- Integrals against a tilted measure: `∫ h d(ρ μ) = ∫ ρ h dμ` for a nonnegative measurable
density `ρ`. -/
theorem integral_withDensity_ofReal_eq {μ : Measure Ω} {ρ : Ω → ℝ} (hρ : Measurable ρ)
    (hρ0 : ∀ ω, 0 ≤ ρ ω) (h : Ω → ℝ) :
    ∫ ω, h ω ∂μ.withDensity (fun ω ↦ ENNReal.ofReal (ρ ω)) = ∫ ω, ρ ω * h ω ∂μ := by
  rw [integral_withDensity_eq_integral_toReal_smul hρ.ennreal_ofReal
    (Eventually.of_forall fun _ ↦ ENNReal.ofReal_lt_top)]
  refine integral_congr_ae (Eventually.of_forall fun ω ↦ ?_)
  simp only [smul_eq_mul, ENNReal.toReal_ofReal (hρ0 ω)]

/-- A function integrable for `μ` is integrable for `ρ μ` when `0 ≤ ρ ≤ R`. -/
theorem integrable_withDensity_ofReal_of_le {μ : Measure Ω} {ρ : Ω → ℝ} (hρ : Measurable ρ)
    (hρ0 : ∀ ω, 0 ≤ ρ ω) {R : ℝ} (hR : ∀ ω, ρ ω ≤ R) {h : Ω → ℝ} (hh : Integrable h μ) :
    Integrable h (μ.withDensity fun ω ↦ ENNReal.ofReal (ρ ω)) := by
  rw [integrable_withDensity_iff_integrable_smul' hρ.ennreal_ofReal
    (Eventually.of_forall fun _ ↦ ENNReal.ofReal_lt_top)]
  have h1 : Integrable (fun ω ↦ h ω * ρ ω) μ :=
    hh.mul_bdd hρ.aestronglyMeasurable (c := R) (Eventually.of_forall fun ω ↦ by
      rw [Real.norm_of_nonneg (hρ0 ω)]; exact hR ω)
  refine h1.congr (Eventually.of_forall fun ω ↦ ?_)
  simp only [smul_eq_mul, ENNReal.toReal_ofReal (hρ0 ω), mul_comm]

/-- **Conditional expectation under a tilted law**: for `ν = ρ μ` with `r ≤ ρ ≤ R`, `0 < r`,
and `f` integrable, `ν[f | X] = μ[ρ f | X] / μ[ρ | X]` almost surely. -/
theorem condExp_withDensity_ofReal_ae_eq {𝒳 : Type*} [MeasurableSpace 𝒳] {X : Ω → 𝒳}
    (hX : Measurable X)
    {μ : Measure Ω} [IsFiniteMeasure μ] {ρ f : Ω → ℝ} (hρ : Measurable ρ) {r R : ℝ} (hr : 0 < r)
    (hlow : ∀ ω, r ≤ ρ ω) (hup : ∀ ω, ρ ω ≤ R) (hf : Integrable f μ) :
    (μ.withDensity fun ω ↦ ENNReal.ofReal (ρ ω))[f | MeasurableSpace.comap X inferInstance]
      =ᵐ[μ] μ[ρ * f | MeasurableSpace.comap X inferInstance] /
        μ[ρ | MeasurableSpace.comap X inferInstance] := by
  have hm : MeasurableSpace.comap X inferInstance ≤ mΩ := hX.comap_le
  set ν := μ.withDensity fun ω ↦ ENNReal.ofReal (ρ ω)
  have hρ0 : ∀ ω, 0 ≤ ρ ω := fun ω ↦ hr.le.trans (hlow ω)
  have hρI : Integrable ρ μ := Integrable.of_bound hρ.aestronglyMeasurable R
    (Eventually.of_forall fun ω ↦ by rw [Real.norm_of_nonneg (hρ0 ω)]; exact hup ω)
  have hfin : IsFiniteMeasure ν := isFiniteMeasure_withDensity_ofReal hρI.2
  have hμν : μ ≪ ν := withDensity_absolutelyContinuous' hρ.ennreal_ofReal.aemeasurable
    (Eventually.of_forall fun ω ↦ by
      rw [Ne, ENNReal.ofReal_eq_zero, not_le]; exact hr.trans_le (hlow ω))
  have hρf : Integrable (ρ * f) μ := by
    have := hf.mul_bdd hρ.aestronglyMeasurable (c := R) (Eventually.of_forall fun ω ↦ by
      rw [Real.norm_of_nonneg (hρ0 ω)]; exact hup ω)
    refine this.congr (Eventually.of_forall fun ω ↦ ?_)
    simp only [Pi.mul_apply, mul_comm]
  -- the denominator is at least `r`
  have hden : ∀ᵐ ω ∂μ, r ≤ μ[ρ | MeasurableSpace.comap X inferInstance] ω := by
    have h := condExp_mono (m := MeasurableSpace.comap X inferInstance) (integrable_const r) hρI
      (Eventually.of_forall hlow)
    rw [condExp_const hm] at h
    exact h
  set g : Ω → ℝ := μ[ρ * f | MeasurableSpace.comap X inferInstance] /
    μ[ρ | MeasurableSpace.comap X inferInstance]
  have hgm : StronglyMeasurable[MeasurableSpace.comap X inferInstance] g :=
    stronglyMeasurable_condExp.div stronglyMeasurable_condExp
  have hinvm : StronglyMeasurable[MeasurableSpace.comap X inferInstance]
      fun ω ↦ (μ[ρ | MeasurableSpace.comap X inferInstance] ω)⁻¹ :=
    (stronglyMeasurable_condExp (m := MeasurableSpace.comap X inferInstance) (μ := μ)
      (f := ρ)).measurable.inv.stronglyMeasurable
  have hgI : Integrable g μ := by
    have hinv : ∀ᵐ ω ∂μ, ‖(μ[ρ | MeasurableSpace.comap X inferInstance] ω)⁻¹‖ ≤ r⁻¹ :=
      hden.mono fun ω h ↦ by
      rw [norm_inv, Real.norm_of_nonneg (hr.le.trans h)]
      exact inv_anti₀ hr h
    have := (integrable_condExp (f := ρ * f) (m := MeasurableSpace.comap X inferInstance)
      (μ := μ)).mul_bdd
      (hinvm.mono hm).aestronglyMeasurable hinv
    exact this.congr (Eventually.of_forall fun ω ↦ by simp [g, div_eq_mul_inv])
  have hgν : Integrable g ν := integrable_withDensity_ofReal_of_le hρ hρ0 hup hgI
  have hfν : Integrable f ν := integrable_withDensity_ofReal_of_le hρ hρ0 hup hf
  have hρg : Integrable (ρ * g) μ := by
    have := hgI.mul_bdd hρ.aestronglyMeasurable (c := R) (Eventually.of_forall fun ω ↦ by
      rw [Real.norm_of_nonneg (hρ0 ω)]; exact hup ω)
    refine this.congr (Eventually.of_forall fun ω ↦ ?_)
    simp only [Pi.mul_apply, mul_comm]
  have hkey : ∀ s, MeasurableSet[MeasurableSpace.comap X inferInstance] s →
      ∫ ω in s, g ω ∂ν = ∫ ω in s, f ω ∂ν := by
    intro s hs
    have hs' : MeasurableSet s := hm s hs
    have e1 : ∀ h : Ω → ℝ, ∫ ω in s, h ω ∂ν = ∫ ω in s, ρ ω * h ω ∂μ := fun h ↦ by
      rw [restrict_withDensity hs']
      exact integral_withDensity_ofReal_eq hρ hρ0 h
    rw [e1, e1]
    calc ∫ ω in s, ρ ω * g ω ∂μ
          = ∫ ω in s, μ[ρ * g | MeasurableSpace.comap X inferInstance] ω ∂μ :=
          (setIntegral_condExp hm hρg hs).symm
      _ = ∫ ω in s, μ[ρ * f | MeasurableSpace.comap X inferInstance] ω ∂μ := by
          refine setIntegral_congr_ae hs' ?_
          filter_upwards [condExp_mul_of_stronglyMeasurable_right hgm hρg hρI, hden]
            with ω h1 h2 _
          rw [h1]
          simp only [Pi.mul_apply, g, Pi.div_apply]
          field_simp [(hr.trans_le h2).ne']
      _ = ∫ ω in s, ρ ω * f ω ∂μ := setIntegral_condExp hm hρf hs
  have hν : g =ᵐ[ν] ν[f | MeasurableSpace.comap X inferInstance] :=
    ae_eq_condExp_of_forall_setIntegral_eq hm hfν (fun s _ _ ↦ hgν.integrableOn)
      (fun s hs _ ↦ hkey s hs) hgm.aestronglyMeasurable
  exact (hμν.ae_eq hν).symm

/-- The tilted conditional mean is affine in the tilt:
`E[(1 + t S) F | m] = E[F | m] + t E[S F | m]` almost surely. -/
theorem condExp_one_add_mul_ae_eq {μ : Measure Ω} (m' : MeasurableSpace Ω) {S F : Ω → ℝ}
    (hF : Integrable F μ) (hSF : Integrable (fun ω ↦ S ω * F ω) μ) (t : ℝ) :
    μ[fun ω ↦ (1 + t * S ω) * F ω | m'] =ᵐ[μ]
      fun ω ↦ μ[F | m'] ω + t * μ[fun ω ↦ S ω * F ω | m'] ω := by
  have e : (fun ω ↦ (1 + t * S ω) * F ω) = F + t • (fun ω ↦ S ω * F ω) := by
    funext ω
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  rw [e]
  filter_upwards [condExp_add hF (hSF.smul t) m',
    condExp_smul (μ := μ) t (fun ω ↦ S ω * F ω) m'] with ω h1 h2
  rw [h1, Pi.add_apply, h2, Pi.smul_apply, smul_eq_mul]

/-- The real bounds behind the dominated limit of the pathwise derivative: if `|a| ≤ K`,
`|c| ≤ K E`, `ε ≤ E ≤ 1` and `|t| K ≤ 1/2`, then `E / 2 ≤ E + t c` and the difference quotient
`(b + a E M - M c + t a b) / (E + t c)` is at most `(2 |b| + 2 K |M|) / (ε / 2)` in absolute
value. -/
theorem abs_tilt_quotient_le {a b c E M t K eps : ℝ} (hK : 0 < K) (heps : 0 < eps)
    (ha : |a| ≤ K) (hc : |c| ≤ K * E) (hE : eps ≤ E) (hE1 : E ≤ 1) (ht : |t| * K ≤ 1 / 2) :
    E / 2 ≤ E + t * c ∧ |(b + a * E * M - M * c + t * a * b) / (E + t * c)| ≤
      (2 * |b| + 2 * K * |M|) / (eps / 2) := by
  have hE0 : 0 ≤ E := heps.le.trans hE
  have htc : |t * c| ≤ E / 2 := by
    rw [abs_mul]
    calc |t| * |c| ≤ |t| * (K * E) := mul_le_mul_of_nonneg_left hc (abs_nonneg t)
      _ = (|t| * K) * E := by ring
      _ ≤ (1 / 2) * E := mul_le_mul_of_nonneg_right ht hE0
      _ = E / 2 := by ring
  have hden : E / 2 ≤ E + t * c := by linarith [neg_abs_le (t * c)]
  refine ⟨hden, ?_⟩
  have hd0 : 0 < E + t * c := by linarith
  have hnum : |b + a * E * M - M * c + t * a * b| ≤ 2 * |b| + 2 * K * |M| := by
    have e : b + a * E * M - M * c + t * a * b = b + a * E * M + -(M * c) + t * a * b := by ring
    rw [e]
    have h1 := abs_add_le (b + a * E * M + -(M * c)) (t * a * b)
    have h2 := abs_add_three b (a * E * M) (-(M * c))
    rw [abs_neg] at h2
    have h3 : |a * E * M| ≤ K * |M| := by
      rw [abs_mul, abs_mul, abs_of_nonneg hE0]
      have : |a| * E ≤ K := by nlinarith [abs_nonneg a]
      exact mul_le_mul_of_nonneg_right this (abs_nonneg M)
    have h4 : |M * c| ≤ K * |M| := by
      rw [abs_mul]
      have : |c| ≤ K := hc.trans (by nlinarith)
      nlinarith [abs_nonneg M]
    have h5 : |t * a * b| ≤ |b| := by
      rw [abs_mul, abs_mul]
      have : |t| * |a| ≤ 1 := by nlinarith [abs_nonneg t]
      nlinarith [abs_nonneg b]
    linarith
  rw [abs_div, abs_of_pos hd0]
  exact div_le_div₀ (by positivity) hnum (by positivity) (by linarith)

end Tilt

section Submodel

variable {Ω : Type*} [mΩ : MeasurableSpace Ω]

/-- The **score submodel** `dμ_t = (1 + t S) dμ` through `μ` in the direction of the score `S`.
For a bounded measurable `S` with `E[S] = 0` and `|t| sup |S| ≤ 1` it is a probability measure
(`isProbabilityMeasure_scoreTilt`), and its score at `t = 0` is `S`. -/
noncomputable def scoreTilt (μ : Measure Ω) (S : Ω → ℝ) (t : ℝ) : Measure Ω :=
  μ.withDensity fun ω ↦ ENNReal.ofReal (1 + t * S ω)

omit mΩ in
theorem one_add_mul_nonneg_of_abs_le {S : Ω → ℝ} {C : ℝ} (hC : ∀ ω, |S ω| ≤ C) {t : ℝ}
    (ht : |t| * C ≤ 1) (ω : Ω) : 0 ≤ 1 + t * S ω := by
  have : |t * S ω| ≤ 1 := by
    rw [abs_mul]
    exact (mul_le_mul_of_nonneg_left (hC _) (abs_nonneg t)).trans ht
  linarith [neg_abs_le (t * S ω)]

/-- **The score submodel is a probability measure**: for a bounded measurable score with
`E[S] = 0` and `|t| C ≤ 1`, `(1 + t S) μ` has total mass one. -/
theorem isProbabilityMeasure_scoreTilt {μ : Measure Ω} [IsProbabilityMeasure μ] {S : Ω → ℝ}
    (hS : Measurable S) {C : ℝ} (hC : ∀ ω, |S ω| ≤ C) (hS0 : ∫ ω, S ω ∂μ = 0) {t : ℝ}
    (ht : |t| * C ≤ 1) : IsProbabilityMeasure (scoreTilt μ S t) := by
  have hSI : Integrable S μ :=
    Integrable.of_bound hS.aestronglyMeasurable C
      (Eventually.of_forall fun ω ↦ by rw [Real.norm_eq_abs]; exact hC _)
  have hI : Integrable (fun ω ↦ 1 + t * S ω) μ := (integrable_const 1).add (hSI.const_mul t)
  constructor
  rw [scoreTilt, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal hI
      (Eventually.of_forall (one_add_mul_nonneg_of_abs_le hC ht)),
    integral_add (integrable_const 1) (hSI.const_mul t), integral_const_mul, hS0]
  simp

end Submodel

end Efficiency
end CausalInference
