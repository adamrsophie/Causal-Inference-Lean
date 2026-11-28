/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.Efficiency.InfluenceFunction

/-!
# The product form of the bias of the augmented summand

For working nuisance functions `ê` and `m̂` (fixed functions, for example fitted on an
independent sample), the mean of the augmented summand of the arm `a` differs from `E[Y(a)]` by
the product remainder
`E[aipwScore ê m̂ a (O)] - E[Y(a)] = E[(π̂_a(W) - π_a(W)) (m̂(a, W) - m(a, W)) / π̂_a(W)]`,
with `π_a = armProb e a` and `π̂_a = armProb ê a`. By the Cauchy-Schwarz inequality its absolute
value is at most `ε'⁻¹ ‖π̂_a - π_a‖₂ ‖m̂(a, ·) - m(a, ·)‖₂` when `π̂_a ≥ ε' > 0`. The bias is
second order: it is the product of the errors of the two nuisance functions.

## Main results

* `integral_mul_le_sqrt_mul_sqrt`: the Cauchy-Schwarz inequality for nonnegative square
  integrable functions.
* `integral_aipwScore_sub_armMean`: the product bias identity.
* `abs_integral_aipwScore_sub_armMean_le`: its Cauchy-Schwarz bound.

## References

* J. M. Robins, A. Rotnitzky and L. P. Zhao, *Estimation of regression coefficients when some
  regressors are not always observed*, Journal of the American Statistical Association 89
  (1994).
* V. Chernozhukov, D. Chetverikov, M. Demirer, E. Duflo, C. Hansen, W. Newey and J. Robins,
  *Double/debiased machine learning for treatment and structural parameters*, The Econometrics
  Journal 21 (2018).
-/

@[expose] public section

namespace CausalInference
namespace Efficiency

open MeasureTheory ProbabilityTheory MissingData PointTreatment Filter

variable {Ω 𝒲 : Type*} {mΩ : MeasurableSpace Ω} [MeasurableSpace 𝒲]
  {A : Ω → Bool} {Y : Bool → Ω → ℝ} {W : Ω → 𝒲} {e : 𝒲 → ℝ} {m : Bool → 𝒲 → ℝ}
  {μ : Measure Ω}

omit [MeasurableSpace 𝒲] in
/-- The Cauchy-Schwarz inequality `∫ f g ≤ √(∫ f²) √(∫ g²)` for nonnegative square integrable
functions. -/
theorem integral_mul_le_sqrt_mul_sqrt {f g : Ω → ℝ} (hf0 : ∀ ω, 0 ≤ f ω) (hg0 : ∀ ω, 0 ≤ g ω)
    (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    ∫ ω, f ω * g ω ∂μ ≤ √(∫ ω, f ω ^ 2 ∂μ) * √(∫ ω, g ω ^ 2 ∂μ) := by
  have h := integral_mul_le_Lp_mul_Lq_of_nonneg Real.HolderConjugate.two_two
    (Eventually.of_forall hf0) (Eventually.of_forall hg0)
    (by rw [ENNReal.ofReal_ofNat]; exact hf) (by rw [ENNReal.ofReal_ofNat]; exact hg)
  rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow]
  simpa only [Real.rpow_two] using h

variable [IsProbabilityMeasure μ]

/-- **The product bias identity.** Under mean ignorability of the arm `a`, a correct score `e`
with `π_a(W) > 0` almost surely and a correct regression `m`, for a measurable working score `ê`
with `π̂_a ≥ ε' > 0` everywhere and a working regression with `m̂(a, W)` square integrable,
`E[aipwScore ê m̂ a (O)] - E[Y(a)] = E[(π̂_a(W) - π_a(W)) (m̂(a, W) - m(a, W)) / π̂_a(W)]`. -/
theorem integral_aipwScore_sub_armMean (hW : Measurable W) (hA : Measurable A)
    (hY2 : ∀ a, MemLp (Y a) 2 μ) (hps : IsPropensityScore μ A W e)
    (hreg : IsOutcomeRegression μ A W (obsOutcome A Y) m) (a : Bool)
    (hmi : MeanIgnorable μ A W Y a) (hpos : ∀ᵐ ω ∂μ, 0 < armProb e a (W ω))
    {e' : 𝒲 → ℝ} {m' : Bool → 𝒲 → ℝ} (he' : Measurable e') (hm' : Measurable (m' a))
    {ε' : ℝ} (hε' : 0 < ε') (he'b : ∀ w, ε' ≤ armProb e' a w)
    (hm'2 : MemLp (fun ω => m' a (W ω)) 2 μ) :
    ∫ ω, aipwScore e' m' a (obsData A Y W ω) ∂μ - armMean μ Y a =
      ∫ ω, (armProb e' a (W ω) - armProb e a (W ω)) * (m' a (W ω) - m a (W ω)) /
        armProb e' a (W ω) ∂μ := by
  have hYi : ∀ a, Integrable (Y a) μ := fun a => (hY2 a).integrable one_le_two
  have hYo := integrable_obsOutcome hA hYi
  have hmW : MeasurableSpace.comap W inferInstance ≤ mΩ := hW.comap_le
  have hid := hreg.ae_eq_condExp hW hA hYi hps a hmi hpos
  have hm2 : MemLp (fun ω => m a (W ω)) 2 μ := ((hY2 a).condExp one_le_two).ae_eq hid.symm
  have hmI := hm2.integrable one_le_two
  have hm'I := hm'2.integrable one_le_two
  have hmAI : Integrable (fun ω => m (A ω) (W ω)) μ := integrable_condExp.congr hreg.2
  have hpos' : ∀ᵐ ω ∂μ, ε' ≤ armProb e' a (W ω) := Eventually.of_forall fun ω => he'b _
  have hR0 := integral_weightedResidual_mul_eq_zero (e := e') hW hA he' hreg hYo a hε' hpos'
    (h := fun _ => 1) measurable_const (by simpa using hYo) (by simpa using hmAI)
  simp only [mul_one] at hR0
  have hRI := integrable_weightedResidual (e := e') hW hA he' hYo hmAI a hε' hpos'
  have hp'm : Measurable fun ω => armProb e' a (W ω) := (measurable_armProb he' a).comp hW
  have hpm : Measurable fun ω => armProb e a (W ω) := (measurable_armProb hps.1 a).comp hW
  have hinv : ∀ ω, ‖(armProb e' a (W ω))⁻¹‖ ≤ ε'⁻¹ := fun ω => by
    rw [norm_inv, Real.norm_of_nonneg (hε'.le.trans (he'b _))]
    exact inv_anti₀ hε' (he'b _)
  have hIcc := hps.ae_mem_Icc hW hA
  have hpb : ∀ᵐ ω ∂μ, ‖armProb e a (W ω)‖ ≤ 1 := hIcc.mono fun ω h => by
    cases a <;> simp only [armProb_true, armProb_false] <;>
      rw [Real.norm_eq_abs, abs_le] <;> constructor <;> linarith [h.1, h.2]
  -- the two functions of `W` whose products with `1{A = a}` occur
  set g₁ : 𝒲 → ℝ := fun w => m a w / armProb e' a w with hg₁
  set g₂ : 𝒲 → ℝ := fun w => m' a w / armProb e' a w with hg₂
  have hg₁m : Measurable g₁ := (hreg.1 a).div (measurable_armProb he' a)
  have hg₂m : Measurable g₂ := hm'.div (measurable_armProb he' a)
  have hg₁I : Integrable (fun ω => g₁ (W ω)) μ :=
    (hmI.mul_bdd hp'm.inv.aestronglyMeasurable (Eventually.of_forall hinv)).congr
      (Eventually.of_forall fun ω => by simp only [hg₁, div_eq_mul_inv, Pi.inv_apply])
  have hg₂I : Integrable (fun ω => g₂ (W ω)) μ :=
    (hm'I.mul_bdd hp'm.inv.aestronglyMeasurable (Eventually.of_forall hinv)).congr
      (Eventually.of_forall fun ω => by simp only [hg₂, div_eq_mul_inv, Pi.inv_apply])
  have hbI : Integrable (respInd (arm A a)) μ := integrable_respInd (measurable_arm hA a)
  have hbm := measurable_respInd (measurable_arm hA a)
  have hb1 : ∀ ω, ‖respInd (arm A a) ω‖ ≤ 1 := fun ω => by
    rw [Real.norm_of_nonneg (respInd_nonneg _ ω)]; exact respInd_le_one _ ω
  have hprop : ∀ {g : 𝒲 → ℝ}, Measurable g → Integrable (fun ω => g (W ω)) μ →
      ∫ ω, respInd (arm A a) ω * g (W ω) ∂μ = ∫ ω, armProb e a (W ω) * g (W ω) ∂μ := by
    intro g hg hgI
    have hgW : StronglyMeasurable[MeasurableSpace.comap W inferInstance] fun ω => g (W ω) :=
      (hg.comp (comap_measurable W)).stronglyMeasurable
    rw [integral_mul_eq_integral_condExp_mul hmW hgW hbI
      ((hgI.bdd_mul hbm.aestronglyMeasurable (Eventually.of_forall hb1)).congr
        (Eventually.of_forall fun _ => rfl))]
    exact integral_congr_ae ((hps.condExp_arm hW hA a).mono fun ω h => by simp only [h])
  have I₁ : Integrable (fun ω => respInd (arm A a) ω * g₁ (W ω)) μ :=
    hg₁I.bdd_mul hbm.aestronglyMeasurable (Eventually.of_forall hb1)
  have I₂ : Integrable (fun ω => respInd (arm A a) ω * g₂ (W ω)) μ :=
    hg₂I.bdd_mul hbm.aestronglyMeasurable (Eventually.of_forall hb1)
  have J₁ : Integrable (fun ω => armProb e a (W ω) * g₁ (W ω)) μ :=
    hg₁I.bdd_mul hpm.aestronglyMeasurable hpb
  have J₂ : Integrable (fun ω => armProb e a (W ω) * g₂ (W ω)) μ :=
    hg₂I.bdd_mul hpm.aestronglyMeasurable hpb
  have hdecomp : ∀ ω, aipwScore e' m' a (obsData A Y W ω) =
      weightedResidual A Y W e' m a ω + respInd (arm A a) ω * g₁ (W ω) -
        respInd (arm A a) ω * g₂ (W ω) + m' a (W ω) := fun ω => by
    have hne : armProb e' a (W ω) ≠ 0 := (hε'.trans_le (he'b _)).ne'
    rw [aipwScore_eq a hne, armIndicator_obsData]
    simp only [obsData, weightedResidual, hg₁, hg₂]
    field_simp
    ring
  have hψ := armMean_eq_integral_regression hW hA hYi hreg hps a hmi hpos
  calc ∫ ω, aipwScore e' m' a (obsData A Y W ω) ∂μ - armMean μ Y a
      = (∫ ω, weightedResidual A Y W e' m a ω ∂μ + ∫ ω, respInd (arm A a) ω * g₁ (W ω) ∂μ -
          ∫ ω, respInd (arm A a) ω * g₂ (W ω) ∂μ + ∫ ω, m' a (W ω) ∂μ) -
          ∫ ω, m a (W ω) ∂μ := by
        rw [hψ, integral_congr_ae (Eventually.of_forall hdecomp),
          integral_add (f := fun ω => weightedResidual A Y W e' m a ω +
            respInd (arm A a) ω * g₁ (W ω) - respInd (arm A a) ω * g₂ (W ω))
            (g := fun ω => m' a (W ω)) ((hRI.add I₁).sub I₂) hm'I,
          integral_sub (f := fun ω => weightedResidual A Y W e' m a ω +
            respInd (arm A a) ω * g₁ (W ω)) (g := fun ω => respInd (arm A a) ω * g₂ (W ω))
            (hRI.add I₁) I₂,
          integral_add (f := weightedResidual A Y W e' m a)
            (g := fun ω => respInd (arm A a) ω * g₁ (W ω)) hRI I₁]
    _ = ∫ ω, armProb e a (W ω) * g₁ (W ω) ∂μ - ∫ ω, armProb e a (W ω) * g₂ (W ω) ∂μ +
          ∫ ω, m' a (W ω) ∂μ - ∫ ω, m a (W ω) ∂μ := by
        rw [hR0, hprop hg₁m hg₁I, hprop hg₂m hg₂I]; ring
    _ = ∫ ω, (armProb e a (W ω) * g₁ (W ω) - armProb e a (W ω) * g₂ (W ω) + m' a (W ω) -
          m a (W ω)) ∂μ := by
        rw [integral_sub (f := fun ω => armProb e a (W ω) * g₁ (W ω) -
            armProb e a (W ω) * g₂ (W ω) + m' a (W ω)) (g := fun ω => m a (W ω))
            ((J₁.sub J₂).add hm'I) hmI,
          integral_add (f := fun ω => armProb e a (W ω) * g₁ (W ω) -
            armProb e a (W ω) * g₂ (W ω)) (g := fun ω => m' a (W ω)) (J₁.sub J₂) hm'I,
          integral_sub (f := fun ω => armProb e a (W ω) * g₁ (W ω))
            (g := fun ω => armProb e a (W ω) * g₂ (W ω)) J₁ J₂]
    _ = _ := by
        refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
        have hne : armProb e' a (W ω) ≠ 0 := (hε'.trans_le (he'b _)).ne'
        simp only [hg₁, hg₂]
        field_simp
        ring

/-- **The Cauchy-Schwarz bound of the product bias**: under the hypotheses of
`integral_aipwScore_sub_armMean`, with also `π̂_a ≤ 1` everywhere,
`|E[aipwScore ê m̂ a (O)] - E[Y(a)]| ≤ ε'⁻¹ ‖π̂_a(W) - π_a(W)‖₂ ‖m̂(a, W) - m(a, W)‖₂`. -/
theorem abs_integral_aipwScore_sub_armMean_le (hW : Measurable W) (hA : Measurable A)
    (hY2 : ∀ a, MemLp (Y a) 2 μ) (hps : IsPropensityScore μ A W e)
    (hreg : IsOutcomeRegression μ A W (obsOutcome A Y) m) (a : Bool)
    (hmi : MeanIgnorable μ A W Y a) (hpos : ∀ᵐ ω ∂μ, 0 < armProb e a (W ω))
    {e' : 𝒲 → ℝ} {m' : Bool → 𝒲 → ℝ} (he' : Measurable e') (hm' : Measurable (m' a))
    {ε' : ℝ} (hε' : 0 < ε') (he'b : ∀ w, ε' ≤ armProb e' a w ∧ armProb e' a w ≤ 1)
    (hm'2 : MemLp (fun ω => m' a (W ω)) 2 μ) :
    |∫ ω, aipwScore e' m' a (obsData A Y W ω) ∂μ - armMean μ Y a| ≤
      ε'⁻¹ * (√(∫ ω, (armProb e' a (W ω) - armProb e a (W ω)) ^ 2 ∂μ) *
        √(∫ ω, (m' a (W ω) - m a (W ω)) ^ 2 ∂μ)) := by
  have hYi : ∀ a, Integrable (Y a) μ := fun a => (hY2 a).integrable one_le_two
  rw [integral_aipwScore_sub_armMean hW hA hY2 hps hreg a hmi hpos he' hm' hε'
    (fun w => (he'b w).1) hm'2]
  have hid := hreg.ae_eq_condExp hW hA hYi hps a hmi hpos
  have hm2 : MemLp (fun ω => m a (W ω)) 2 μ := ((hY2 a).condExp one_le_two).ae_eq hid.symm
  have hIcc := hps.ae_mem_Icc hW hA
  have hd1 : MemLp (fun ω => armProb e' a (W ω) - armProb e a (W ω)) 2 μ := by
    refine MemLp.of_bound (((measurable_armProb he' a).comp hW).sub
      ((measurable_armProb hps.1 a).comp hW)).aestronglyMeasurable 1 (hIcc.mono fun ω h => ?_)
    have h' := he'b (W ω)
    rw [Real.norm_eq_abs, abs_le]
    cases a <;> simp only [armProb_true, armProb_false] at h' ⊢ <;> constructor <;>
      linarith [h.1, h.2, h'.1, h'.2]
  have hd2 : MemLp (fun ω => m' a (W ω) - m a (W ω)) 2 μ := hm'2.sub hm2
  have hcs := integral_mul_le_sqrt_mul_sqrt (μ := μ)
    (fun ω => abs_nonneg (armProb e' a (W ω) - armProb e a (W ω)))
    (fun ω => abs_nonneg (m' a (W ω) - m a (W ω))) hd1.abs hd2.abs
  simp only [sq_abs] at hcs
  have hprodI : Integrable (fun ω => |armProb e' a (W ω) - armProb e a (W ω)| *
      |m' a (W ω) - m a (W ω)|) μ := hd1.abs.integrable_mul hd2.abs
  calc |∫ ω, (armProb e' a (W ω) - armProb e a (W ω)) * (m' a (W ω) - m a (W ω)) /
        armProb e' a (W ω) ∂μ|
      ≤ ∫ ω, |(armProb e' a (W ω) - armProb e a (W ω)) * (m' a (W ω) - m a (W ω)) /
          armProb e' a (W ω)| ∂μ := abs_integral_le_integral_abs
    _ ≤ ∫ ω, ε'⁻¹ * (|armProb e' a (W ω) - armProb e a (W ω)| * |m' a (W ω) - m a (W ω)|)
          ∂μ := by
        refine integral_mono_of_nonneg (Eventually.of_forall fun ω => abs_nonneg _)
          (hprodI.const_mul _) (Eventually.of_forall fun ω => ?_)
        have hp : 0 < armProb e' a (W ω) := hε'.trans_le (he'b _).1
        dsimp only
        rw [abs_div, abs_mul, abs_of_pos hp, div_eq_mul_inv, mul_comm]
        exact mul_le_mul_of_nonneg_right (inv_anti₀ hε' (he'b _).1) (by positivity)
    _ ≤ _ := by
        rw [integral_const_mul]
        exact mul_le_mul_of_nonneg_left hcs (inv_nonneg.mpr hε'.le)

end Efficiency
end CausalInference
