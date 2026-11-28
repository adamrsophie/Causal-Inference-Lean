/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.NetworkMetaRegression.UnanchoredSurvivalLikelihood
public import Mathlib.Probability.CDF
public import Mathlib.Probability.ConditionalProbability
public import Mathlib.Analysis.Calculus.Deriv.Slope
public import Mathlib.Topology.Order.LeftRightLim
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.LebesgueDifferentiationThm

/-!
# The conditional hazard as a limit

**Time scale: continuous.** For an event time law `μ` on `ℝ` with distribution function `F`,
the hazard at `t` is the limit of `P(t < T ≤ t + Δ | T > t) / Δ` as `Δ ↓ 0`. The limit exists and
is the hazard `curveHazard (1 - F) t = F'(t) / (1 - F(t))` of the survival curve at every `t` with
`F(t) < 1` where `F` is differentiable (`tendsto_cond_Ioc_div`); no density is needed.
Differentiability of `F` at `t` rules out an atom at `t`
(`measure_singleton_eq_zero_of_hasDerivAt`); for a law without atoms the form
`P(t ≤ T < t + Δ | T ≥ t) / Δ` has the same limit (`tendsto_cond_Ico_div`). For a law with a
density `g`, `F' = g` at every continuity point of `g` and almost everywhere
(`hasDerivAt_cdf_withDensity`, `ae_hasDerivAt_cdf_withDensity`), so the limit holds at every
continuity point and at almost every time with `F(t) < 1`.

## Main results

* `tendsto_cond_Ioc_div`, `tendsto_cond_Ico_div`, `curveHazard_one_sub_cdf_mul`.
* `hasDerivAt_cdf_withDensity`, `ae_hasDerivAt_cdf_withDensity`,
  `tendsto_cond_Ioc_div_withDensity`.
* `tendsto_cond_Ioc_div_phEventLaw`: under the proportional hazards model the limit is the
  conditional hazard `r h₀(t)`; `hazardLimit_instance` computes it for a unit baseline.
-/

@[expose] public section

namespace CausalInference

namespace NetworkMetaRegression

open MeasureTheory ProbabilityTheory Filter Topology Set
open Survival.ContinuousTime
open scoped ENNReal

variable {μ : Measure ℝ} [IsProbabilityMeasure μ]

theorem measureReal_Ioi_eq_one_sub_cdf (t : ℝ) : μ.real (Ioi t) = 1 - cdf μ t := by
  rw [← compl_Iic, probReal_compl_eq_one_sub measurableSet_Iic, ← cdf_eq_real]

theorem measureReal_Ioc_eq_cdf_sub {a b : ℝ} (hab : a ≤ b) :
    μ.real (Ioc a b) = cdf μ b - cdf μ a := by
  have e : Ioc a b = Iic b \ Iic a := by
    ext x; simp only [mem_Ioc, Set.mem_sdiff, mem_Iic, not_le]; exact and_comm
  rw [e, measureReal_sdiff (Iic_subset_Iic.2 hab) measurableSet_Iic, cdf_eq_real,
    cdf_eq_real]

/-- The conditional probability `P(t < T ≤ t + Δ | T > t)`, `Δ ≥ 0`, is
`(F(t + Δ) - F(t)) / (1 - F(t))`. -/
theorem cond_real_Ioc {t Δ : ℝ} (hΔ : 0 ≤ Δ) :
    (μ[|Ioi t]).real (Ioc t (t + Δ)) = (cdf μ (t + Δ) - cdf μ t) / (1 - cdf μ t) := by
  rw [measureReal_def, cond_apply measurableSet_Ioi, inter_eq_right.2 Ioc_subset_Ioi_self,
    ENNReal.toReal_mul, ENNReal.toReal_inv, ← measureReal_def, ← measureReal_def,
    measureReal_Ioi_eq_one_sub_cdf, measureReal_Ioc_eq_cdf_sub (by linarith)]
  ring

omit [IsProbabilityMeasure μ] in
/-- **The hazard of the survival curve**: where `F(t) < 1` and `F` has derivative `f` at `t`,
`curveHazard (1 - F) t · (1 - F(t)) = f`. -/
theorem curveHazard_one_sub_cdf_mul {t f : ℝ} (hF : cdf μ t < 1) (hd : HasDerivAt (cdf μ) f t) :
    curveHazard (fun s => 1 - cdf μ s) t * (1 - cdf μ t) = f := by
  have h2 : HasDerivAt (fun s => 1 - cdf μ s) (0 - f) t := (hasDerivAt_const t (1 : ℝ)).sub hd
  rw [curveHazard, h2.deriv, div_mul_cancel₀ _ (by linarith)]
  ring

/-- **The hazard as a limit of conditional probabilities.** At a time `t` with `F(t) < 1` where
the distribution function has a derivative `f`,
`P(t < T ≤ t + Δ | T > t) / Δ → curveHazard (1 - F) t = f / (1 - F(t))` as `Δ ↓ 0`. -/
theorem tendsto_cond_Ioc_div {t f : ℝ} (hF : cdf μ t < 1) (hd : HasDerivAt (cdf μ) f t) :
    Tendsto (fun Δ => (μ[|Ioi t]).real (Ioc t (t + Δ)) / Δ) (𝓝[>] 0)
      (𝓝 (curveHazard (fun s => 1 - cdf μ s) t)) := by
  rw [eq_div_of_mul_eq (by linarith) (curveHazard_one_sub_cdf_mul hF hd)]
  have hs := (hasDerivAt_iff_tendsto_slope_zero.1 hd).mono_left
    (nhdsWithin_mono _ fun Δ h => mem_compl_singleton_iff.2 (mem_Ioi.1 h).ne')
  refine (hs.div_const (1 - cdf μ t)).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with Δ (hΔ : 0 < Δ)
  rw [cond_real_Ioc hΔ.le, smul_eq_mul]
  have : 1 - cdf μ t ≠ 0 := by linarith
  field_simp

/-- Differentiability of the distribution function at `t` rules out an atom at `t`. -/
theorem measure_singleton_eq_zero_of_hasDerivAt {t f : ℝ} (hd : HasDerivAt (cdf μ) f t) :
    μ {t} = 0 := by
  have hl : Function.leftLim (cdf μ) t = cdf μ t :=
    leftLim_eq_of_tendsto (hd.continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
  rw [← measure_cdf (μ := μ), StieltjesFunction.measure_singleton, hl, sub_self,
    ENNReal.ofReal_zero]

/-- **The hazard limit with closed intervals at `t`**: for an event time law without atoms,
under the hypotheses of `tendsto_cond_Ioc_div`,
`P(t ≤ T < t + Δ | T ≥ t) / Δ → curveHazard (1 - F) t` as `Δ ↓ 0`. -/
theorem tendsto_cond_Ico_div [NullSingletonClass μ] {t f : ℝ} (hF : cdf μ t < 1)
    (hd : HasDerivAt (cdf μ) f t) :
    Tendsto (fun Δ => (μ[|Ici t]).real (Ico t (t + Δ)) / Δ) (𝓝[>] 0)
      (𝓝 (curveHazard (fun s => 1 - cdf μ s) t)) := by
  refine (tendsto_cond_Ioc_div hF hd).congr' (Eventually.of_forall fun Δ => ?_)
  simp only [measureReal_def, cond_apply measurableSet_Ici, cond_apply measurableSet_Ioi,
    inter_eq_right.2 Ico_subset_Ici_self, inter_eq_right.2 Ioc_subset_Ioi_self,
    measure_congr (Ioi_ae_eq_Ici (μ := μ) (a := t)), measure_congr (Ico_ae_eq_Ioc (μ := μ)
      (a := t) (b := t + Δ))]

/-! ### Laws with a density -/

section Density

variable {g : ℝ → ℝ}

/-- For a probability law with a nonnegative measurable density `g`,
`F(b) - F(a) = ∫ₐᵇ g` for all `a, b`. -/
theorem cdf_sub_eq_intervalIntegral (hgm : Measurable g) (hg0 : ∀ x, 0 ≤ g x)
    [IsProbabilityMeasure (volume.withDensity fun x => ENNReal.ofReal (g x))] (a b : ℝ) :
    cdf (volume.withDensity fun x => ENNReal.ofReal (g x)) b -
        cdf (volume.withDensity fun x => ENNReal.ofReal (g x)) a = ∫ u in a..b, g u := by
  have key : ∀ a b : ℝ, a ≤ b → cdf (volume.withDensity fun x => ENNReal.ofReal (g x)) b -
      cdf (volume.withDensity fun x => ENNReal.ofReal (g x)) a = ∫ u in a..b, g u := by
    intro a b hab
    rw [← measureReal_Ioc_eq_cdf_sub hab, intervalIntegral.integral_of_le hab, measureReal_def,
      withDensity_apply _ measurableSet_Ioc, integral_eq_lintegral_of_nonneg_ae
        (Eventually.of_forall hg0) hgm.aestronglyMeasurable]
  rcases le_total a b with h | h
  · exact key a b h
  · rw [intervalIntegral.integral_symm, ← key b a h]
    ring

theorem integrable_of_isProbabilityMeasure_withDensity (hgm : Measurable g) (hg0 : ∀ x, 0 ≤ g x)
    [IsProbabilityMeasure (volume.withDensity fun x => ENNReal.ofReal (g x))] : Integrable g := by
  refine ⟨hgm.aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal (Eventually.of_forall hg0)]
  have := measure_univ (μ := volume.withDensity fun x => ENNReal.ofReal (g x))
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ] at this
  rw [this]
  exact ENNReal.one_lt_top

/-- **The distribution function of a law with a density `g` has derivative `g(t)`** at every
continuity point `t` of `g`. -/
theorem hasDerivAt_cdf_withDensity (hgm : Measurable g) (hg0 : ∀ x, 0 ≤ g x)
    [IsProbabilityMeasure (volume.withDensity fun x => ENNReal.ofReal (g x))] {t : ℝ}
    (hc : ContinuousAt g t) :
    HasDerivAt (cdf (volume.withDensity fun x => ENNReal.ofReal (g x))) (g t) t := by
  set ν := volume.withDensity fun x => ENNReal.ofReal (g x)
  have hint := integrable_of_isProbabilityMeasure_withDensity hgm hg0
  have hfun : (cdf ν : ℝ → ℝ) = fun x => cdf ν 0 + ∫ u in (0 : ℝ)..x, g u := by
    funext x
    rw [← cdf_sub_eq_intervalIntegral hgm hg0]
    ring
  rw [hfun]
  exact (intervalIntegral.integral_hasDerivAt_right hint.intervalIntegrable
    hgm.stronglyMeasurable.stronglyMeasurableAtFilter hc).const_add _

/-- **The hazard limit for a law with a density**: at a continuity point `t` of the density `g`
with `F(t) < 1`, `P(t < T ≤ t + Δ | T > t) / Δ → curveHazard (1 - F) t = g(t) / (1 - F(t))` as
`Δ ↓ 0`. -/
theorem tendsto_cond_Ioc_div_withDensity (hgm : Measurable g) (hg0 : ∀ x, 0 ≤ g x)
    [IsProbabilityMeasure (volume.withDensity fun x => ENNReal.ofReal (g x))] {t : ℝ}
    (hc : ContinuousAt g t) (hF : cdf (volume.withDensity fun x => ENNReal.ofReal (g x)) t < 1) :
    Tendsto (fun Δ => ((volume.withDensity fun x => ENNReal.ofReal (g x))[|Ioi t]).real
        (Ioc t (t + Δ)) / Δ) (𝓝[>] 0)
      (𝓝 (curveHazard (fun s => 1 - cdf (volume.withDensity fun x => ENNReal.ofReal (g x)) s) t))
    := tendsto_cond_Ioc_div hF (hasDerivAt_cdf_withDensity hgm hg0 hc)

/-- **Almost every time**: for a law with a nonnegative measurable density `g`, at almost every
`t` the distribution function has derivative `g(t)`, so the hazard limit
`P(t < T ≤ t + Δ | T > t) / Δ → curveHazard (1 - F) t` holds at almost every `t` with
`F(t) < 1`. -/
theorem ae_tendsto_cond_Ioc_div_withDensity (hgm : Measurable g) (hg0 : ∀ x, 0 ≤ g x)
    [IsProbabilityMeasure (volume.withDensity fun x => ENNReal.ofReal (g x))] :
    ∀ᵐ t, HasDerivAt (cdf (volume.withDensity fun x => ENNReal.ofReal (g x))) (g t) t ∧
      (cdf (volume.withDensity fun x => ENNReal.ofReal (g x)) t < 1 →
        Tendsto (fun Δ => ((volume.withDensity fun x => ENNReal.ofReal (g x))[|Ioi t]).real
          (Ioc t (t + Δ)) / Δ) (𝓝[>] 0)
          (𝓝 (curveHazard (fun s => 1 -
            cdf (volume.withDensity fun x => ENNReal.ofReal (g x)) s) t))) := by
  set ν := volume.withDensity fun x => ENNReal.ofReal (g x)
  have hint := integrable_of_isProbabilityMeasure_withDensity hgm hg0
  have hfun : (cdf ν : ℝ → ℝ) = fun x => cdf ν 0 + ∫ u in (0 : ℝ)..x, g u := by
    funext x
    rw [← cdf_sub_eq_intervalIntegral hgm hg0]
    ring
  filter_upwards [LocallyIntegrable.ae_hasDerivAt_integral hint.locallyIntegrable] with t ht
  have hd : HasDerivAt (cdf ν) (g t) t := by
    rw [hfun]
    exact (ht 0).const_add _
  exact ⟨hd, fun hF => tendsto_cond_Ioc_div hF hd⟩

end Density

/-! ### The proportional hazards model -/

section Proportional

variable {h₀ : ℝ → ℝ}

/-- **The hazard limit under proportional hazards.** For a continuous baseline hazard,
nonnegative at nonnegative times, with `H₀ → ∞`, a relative hazard `r > 0` and a time `t > 0`,
`P(t < T ≤ t + Δ | T > t) / Δ → r h₀(t)` as `Δ ↓ 0` under the event time law
`phEventLaw h₀ r`. -/
theorem tendsto_cond_Ioc_div_phEventLaw (hcont : Continuous h₀) (hnn : ∀ u, 0 ≤ u → 0 ≤ h₀ u)
    (hH : Tendsto (cumHazard h₀) atTop atTop) {r : ℝ} (hr : 0 < r) {t : ℝ} (ht : 0 < t) :
    Tendsto (fun Δ => ((phEventLaw h₀ r)[|Ioi t]).real (Ioc t (t + Δ)) / Δ) (𝓝[>] 0)
      (𝓝 (r * h₀ t)) := by
  have : IsProbabilityMeasure (volume.withDensity fun x => ENNReal.ofReal (phDensity h₀ r x)) :=
    isProbabilityMeasure_phEventLaw hcont hnn hH hr
  have := isProbabilityMeasure_phEventLaw hcont hnn hH hr
  have hm : Measurable (phDensity h₀ r) :=
    (measurable_phDensity_uncurry hcont).comp (measurable_const.prodMk measurable_id)
  have hcH := continuous_cumHazard (h₀ := h₀) fun a b => hcont.intervalIntegrable a b
  have hc : ContinuousAt (phDensity h₀ r) t := by
    have heq : (fun u => r * h₀ u * Real.exp (-(r * cumHazard h₀ u))) =ᶠ[𝓝 t] phDensity h₀ r := by
      filter_upwards [lt_mem_nhds ht] with u hu
      rw [phDensity, ite_eq_left hu]
    exact (by fun_prop : Continuous fun u => r * h₀ u * Real.exp (-(r * cumHazard h₀ u)))
      |>.continuousAt.congr heq
  have hS : 1 - cdf (phEventLaw h₀ r) t = Real.exp (-(r * cumHazard h₀ t)) := by
    rw [← measureReal_Ioi_eq_one_sub_cdf, phEventLaw_real_Ioi hcont hnn hH hr,
      max_eq_left ht.le]
  have hF : cdf (phEventLaw h₀ r) t < 1 := by
    have := Real.exp_pos (-(r * cumHazard h₀ t))
    linarith
  have hd : HasDerivAt (cdf (phEventLaw h₀ r)) (phDensity h₀ r t) t :=
    hasDerivAt_cdf_withDensity hm (phDensity_nonneg hnn hr.le) hc
  have h := tendsto_cond_Ioc_div hF hd
  rw [eq_div_of_mul_eq (by linarith) (curveHazard_one_sub_cdf_mul hF hd), hS, phDensity,
    ite_eq_left ht, mul_div_assoc, div_self (Real.exp_pos _).ne', mul_one] at h
  exact h

/-- **Instance: a unit baseline hazard.** With `h₀ = 1` and relative hazard `2` (the second
value of the two valued covariate of `phLikelihood_instance`), at every `t > 0` the distribution
function is `1 - e^{-2t} < 1`, and both `P(t < T ≤ t + Δ | T > t) / Δ` and
`P(t ≤ T < t + Δ | T ≥ t) / Δ` tend to `2` (`tendsto_cond_Ioc_div_phEventLaw`,
`tendsto_cond_Ico_div`, the law having a density and so no atoms). -/
theorem hazardLimit_instance {t : ℝ} (ht : 0 < t) :
    cdf (phEventLaw (fun _ => 1) 2) t = 1 - Real.exp (-(2 * t)) ∧
      Tendsto (fun Δ => ((phEventLaw (fun _ => 1) 2)[|Ioi t]).real (Ioc t (t + Δ)) / Δ)
        (𝓝[>] 0) (𝓝 2) ∧
      Tendsto (fun Δ => ((phEventLaw (fun _ => 1) 2)[|Ici t]).real (Ico t (t + Δ)) / Δ)
        (𝓝[>] 0) (𝓝 2) := by
  have hP : IsProbabilityMeasure (volume.withDensity fun x =>
      ENNReal.ofReal (phDensity (fun _ => (1 : ℝ)) 2 x)) :=
    isProbabilityMeasure_phEventLaw (h₀ := fun _ => 1) continuous_const
      (fun _ _ => zero_le_one) tendsto_cumHazard_one two_pos
  have := isProbabilityMeasure_phEventLaw (h₀ := fun _ => 1) continuous_const
    (fun _ _ => zero_le_one) tendsto_cumHazard_one two_pos
  have hF : cdf (phEventLaw (fun _ => 1) 2) t = 1 - Real.exp (-(2 * t)) := by
    have h := measureReal_Ioi_eq_one_sub_cdf (μ := phEventLaw (fun _ => 1) 2) t
    rw [(phLikelihood_instance ht).1] at h
    linarith
  have hIoc := tendsto_cond_Ioc_div_phEventLaw (h₀ := fun _ => 1) continuous_const
    (fun _ _ => zero_le_one) tendsto_cumHazard_one two_pos ht
  rw [mul_one] at hIoc
  have hm : Measurable (phDensity (fun _ => (1 : ℝ)) 2) :=
    (measurable_phDensity_uncurry continuous_const).comp (measurable_const.prodMk measurable_id)
  have hc : ContinuousAt (phDensity (fun _ => (1 : ℝ)) 2) t := by
    have heq : (fun u => 2 * 1 * Real.exp (-(2 * cumHazard (fun _ => (1 : ℝ)) u))) =ᶠ[𝓝 t]
        phDensity (fun _ => 1) 2 := by
      filter_upwards [lt_mem_nhds ht] with u hu
      rw [phDensity, ite_eq_left hu]
    have hcH := continuous_cumHazard (h₀ := fun _ : ℝ => (1 : ℝ))
      fun a b => intervalIntegrable_const
    exact (by fun_prop : Continuous fun u => 2 * 1 * Real.exp
      (-(2 * cumHazard (fun _ : ℝ => (1 : ℝ)) u))).continuousAt.congr heq
  have hd : HasDerivAt (cdf (phEventLaw (fun _ => 1) 2)) (phDensity (fun _ => 1) 2 t) t :=
    hasDerivAt_cdf_withDensity hm (phDensity_nonneg (fun _ _ => zero_le_one) two_pos.le) hc
  have hlt : cdf (phEventLaw (fun _ => 1) 2) t < 1 := by
    rw [hF]
    linarith [Real.exp_pos (-(2 * t))]
  have hnull : NullSingletonClass (phEventLaw (fun _ => 1) 2) :=
    inferInstanceAs (NullSingletonClass (volume.withDensity fun x =>
      ENNReal.ofReal (phDensity (fun _ => (1 : ℝ)) 2 x)))
  have hv : curveHazard (fun s => 1 - cdf (phEventLaw (fun _ => 1) 2) s) t = 2 :=
    tendsto_nhds_unique (tendsto_cond_Ioc_div hlt hd) hIoc
  refine ⟨hF, hIoc, ?_⟩
  have h := tendsto_cond_Ico_div hlt hd
  rwa [hv] at h

end Proportional

end NetworkMetaRegression

end CausalInference
