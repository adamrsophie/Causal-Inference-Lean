/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.NetworkMetaRegression.UnanchoredSurvivalTarget
public import CausalInference.NetworkMetaRegression.AggregationIdentity
public import CausalInference.Estimation.Consistency
public import CausalInference.Estimation.ConvergenceInProbability
public import Mathlib.Analysis.Calculus.MeanValue

/-!
# The error of an estimated target survival

**Time scale: continuous.** The target survival of an unanchored comparison under the
proportional hazards model with the linear predictor `c + xᵀb` is
`S(ξ, t) = ∫ exp(-e^{c + xᵀb} H₀(t)) F(dx)`, `ξ = (c, b)`. An estimate `Ŝ` of `S(ξ, t)` is computed
at an estimated parameter `ξ̂`, with a numerical integration over `F`. Its error splits into a
numerical part and an estimation part,
`|Ŝ - S(ξ, t)| ≤ |Ŝ - S(ξ̂, t)| + |S(ξ̂, t) - S(ξ, t)|`,
and the estimation part is Lipschitz in the parameter:
`|S(ξ̂, t) - S(ξ, t)| ≤ e^{-1} (1 + ∫ Σⱼ |xⱼ| F(dx)) ‖ξ̂ - ξ‖` (`abs_targetSurvival_sub_le`),
whatever the baseline hazard. Two consequences follow:

* a **rate**: a numerical error at most `C aₙ` and a parameter error at most `rₙ` give the error
  bound `C aₙ + e^{-1} (1 + ∫ Σⱼ |xⱼ|) rₙ` (`abs_targetSurvival_error_le`);
* **consistency**: if `ξ̂ₙ → ξ` in probability and the numerical error is at most `C aₙ` with
  `aₙ → 0`, then `Ŝₙ → S(ξ, t)` in probability (`tendstoInMeasure_targetSurvival`).

## Main definitions

* `targetSurvival`.
-/

@[expose] public section

namespace CausalInference

namespace NetworkMetaRegression

open MeasureTheory Filter Topology Set
open Survival.ContinuousTime

variable {p : ℕ}

/-- The **target survival** `∫ exp(-e^{c + xᵀb} H₀(t)) F(dx)` at the parameter `ξ = (c, b)`. -/
noncomputable def targetSurvival (h₀ : ℝ → ℝ) (F : Measure (Fin p → ℝ)) (ξ : ℝ × (Fin p → ℝ))
    (t : ℝ) : ℝ :=
  popSurvival F (phSurvival (cumHazard h₀) (linearRelativeHazard ξ.1 ξ.2)) t

/-- The map `a ↦ exp(-e^a H)` is `e^{-1}` Lipschitz for `H ≥ 0`. -/
theorem abs_exp_neg_exp_mul_sub_le {H : ℝ} (hH : 0 ≤ H) (a a' : ℝ) :
    |Real.exp (-(Real.exp a' * H)) - Real.exp (-(Real.exp a * H))| ≤
      Real.exp (-1) * |a' - a| := by
  have hd : ∀ y, HasDerivAt (fun a => Real.exp (-(Real.exp a * H)))
      (Real.exp (-(Real.exp y * H)) * -(Real.exp y * H)) y := fun y =>
    (((Real.hasDerivAt_exp y).mul_const H).neg).exp
  have h := convex_univ.norm_image_sub_le_of_norm_deriv_le (f := fun a => Real.exp (-(Real.exp a *
    H))) (C := Real.exp (-1)) (fun y _ => (hd y).differentiableAt) (fun y _ => by
      rw [(hd y).deriv, norm_mul, norm_neg, Real.norm_eq_abs, Real.norm_eq_abs,
        abs_of_pos (Real.exp_pos _), abs_of_nonneg (mul_nonneg (Real.exp_pos y).le hH), mul_comm]
      exact Real.mul_exp_neg_le_exp_neg_one _) (mem_univ a) (mem_univ a')
  simpa only [Real.norm_eq_abs] using h

theorem abs_dotProduct_le_mul_norm (x b : Fin p → ℝ) : |x ⬝ᵥ b| ≤ (∑ j, |x j|) * ‖b‖ := by
  rw [dotProduct, Finset.sum_mul]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => ?_)
  rw [abs_mul]
  exact mul_le_mul_of_nonneg_left (by simpa [Real.norm_eq_abs] using norm_le_pi_norm b j)
    (abs_nonneg _)

/-- **The estimation error is Lipschitz in the parameter.** For a baseline hazard with
`H₀(t) ≥ 0`, a covariate probability law `F` with `∫ Σⱼ |xⱼ| dF < ∞` and parameters `ξ`, `ξ'`,
`|S(ξ', t) - S(ξ, t)| ≤ e^{-1} (1 + ∫ Σⱼ |xⱼ| F(dx)) ‖ξ' - ξ‖`. -/
theorem abs_targetSurvival_sub_le {h₀ : ℝ → ℝ} {t : ℝ} (hH : 0 ≤ cumHazard h₀ t)
    (F : Measure (Fin p → ℝ)) [IsProbabilityMeasure F]
    (hint : Integrable (fun x => ∑ j, |x j|) F) (ξ ξ' : ℝ × (Fin p → ℝ)) :
    |targetSurvival h₀ F ξ' t - targetSurvival h₀ F ξ t| ≤
      Real.exp (-1) * (1 + ∫ x, ∑ j, |x j| ∂F) * ‖ξ' - ξ‖ := by
  set f : ℝ × (Fin p → ℝ) → (Fin p → ℝ) → ℝ := fun ζ x =>
    Real.exp (-(Real.exp (ζ.1 + x ⬝ᵥ ζ.2) * cumHazard h₀ t)) with hf
  have hfi : ∀ ζ, Integrable (f ζ) F := fun ζ =>
    Integrable.of_bound (Continuous.aestronglyMeasurable (by
      simp only [hf, dotProduct]; fun_prop)) 1 (ae_of_all _ fun x => by
        rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), Real.exp_le_one_iff, neg_nonpos]
        exact mul_nonneg (Real.exp_pos _).le hH)
  have e : ∀ ζ, targetSurvival h₀ F ζ t = ∫ x, f ζ x ∂F := fun ζ => rfl
  have hpt : ∀ x, ‖f ξ' x - f ξ x‖ ≤
      Real.exp (-1) * ‖ξ' - ξ‖ + Real.exp (-1) * ‖ξ' - ξ‖ * ∑ j, |x j| := fun x => by
    rw [Real.norm_eq_abs]
    refine (abs_exp_neg_exp_mul_sub_le hH _ _).trans ?_
    have h1 : |ξ'.1 - ξ.1| ≤ ‖ξ' - ξ‖ := by
      simpa [Real.norm_eq_abs] using norm_fst_le (ξ' - ξ)
    have h2 : ‖ξ'.2 - ξ.2‖ ≤ ‖ξ' - ξ‖ := by simpa using norm_snd_le (ξ' - ξ)
    have h3 := abs_dotProduct_le_mul_norm x (ξ'.2 - ξ.2)
    have h4 : |ξ'.1 + x ⬝ᵥ ξ'.2 - (ξ.1 + x ⬝ᵥ ξ.2)| ≤
        ‖ξ' - ξ‖ + ‖ξ' - ξ‖ * ∑ j, |x j| := by
      rw [show ξ'.1 + x ⬝ᵥ ξ'.2 - (ξ.1 + x ⬝ᵥ ξ.2) = (ξ'.1 - ξ.1) + x ⬝ᵥ (ξ'.2 - ξ.2) by
        rw [dotProduct_sub]; ring]
      refine (abs_add_le _ _).trans (add_le_add h1 (h3.trans ?_))
      rw [mul_comm]
      exact mul_le_mul_of_nonneg_right h2 (Finset.sum_nonneg fun j _ => abs_nonneg _)
    calc Real.exp (-1) * |ξ'.1 + x ⬝ᵥ ξ'.2 - (ξ.1 + x ⬝ᵥ ξ.2)|
        ≤ Real.exp (-1) * (‖ξ' - ξ‖ + ‖ξ' - ξ‖ * ∑ j, |x j|) :=
          mul_le_mul_of_nonneg_left h4 (Real.exp_pos _).le
      _ = _ := by ring
  rw [e, e, ← integral_sub (hfi ξ') (hfi ξ), ← Real.norm_eq_abs]
  refine (norm_integral_le_of_norm_le ((integrable_const _).add (hint.const_mul _))
    (ae_of_all _ hpt)).trans_eq ?_
  simp only [Pi.add_apply]
  rw [integral_add (integrable_const _) (hint.const_mul _),
    integral_const_mul (Real.exp (-1) * ‖ξ' - ξ‖) fun x : Fin p → ℝ => ∑ j, |x j|]
  simp only [integral_const, probReal_univ, smul_eq_mul, one_mul]
  ring

/-- **A rate for the error of an estimated target survival**: the error splits into the
numerical error at the estimated parameter and the estimation error, so if the numerical error
is at most `ε_num` and the parameter error is at most `r`, the error is at most
`ε_num + e^{-1} (1 + ∫ Σⱼ |xⱼ| F(dx)) r`. -/
theorem abs_targetSurvival_error_le {h₀ : ℝ → ℝ} {t : ℝ} (hH : 0 ≤ cumHazard h₀ t)
    (F : Measure (Fin p → ℝ)) [IsProbabilityMeasure F]
    (hint : Integrable (fun x => ∑ j, |x j|) F) {ξ ξhat : ℝ × (Fin p → ℝ)} {Shat εnum r : ℝ}
    (hnum : |Shat - targetSurvival h₀ F ξhat t| ≤ εnum) (hr : ‖ξhat - ξ‖ ≤ r) :
    |Shat - targetSurvival h₀ F ξ t| ≤
      εnum + Real.exp (-1) * (1 + ∫ x, ∑ j, |x j| ∂F) * r := by
  have hK : 0 ≤ Real.exp (-1) * (1 + ∫ x, ∑ j, |x j| ∂F) :=
    mul_nonneg (Real.exp_pos _).le (by
      have := integral_nonneg (μ := F) fun x : Fin p → ℝ =>
        Finset.sum_nonneg fun j (_ : j ∈ Finset.univ) => abs_nonneg (x j)
      linarith)
  refine (abs_sub_le Shat (targetSurvival h₀ F ξhat t) _).trans (add_le_add hnum ?_)
  exact (abs_targetSurvival_sub_le hH F hint ξ ξhat).trans (mul_le_mul_of_nonneg_left hr hK)

/-- **Consistency of an estimated target survival.** Let `h₀` be locally integrable and
nonnegative at nonnegative times, `F` a covariate probability law, `t ≥ 0`, and let the estimated
parameters `ξ̂ₙ` converge in probability to `ξ`. If the computed survivals `Ŝₙ` have numerical
error at most `C aₙ` at `ξ̂ₙ`, with `aₙ → 0`, then `Ŝₙ → S(ξ, t)` in probability. -/
theorem tendstoInMeasure_targetSurvival {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsFiniteMeasure P] {h₀ : ℝ → ℝ} (hloc : ∀ a b, IntervalIntegrable h₀ volume a b)
    (hnn : ∀ u, 0 ≤ u → 0 ≤ h₀ u) (F : Measure (Fin p → ℝ)) [IsProbabilityMeasure F] {t : ℝ}
    (ht : 0 ≤ t) {ξ : ℝ × (Fin p → ℝ)} {ξhat : ℕ → Ω → ℝ × (Fin p → ℝ)}
    (hξ : TendstoInMeasure P ξhat atTop fun _ => ξ) {Shat : ℕ → Ω → ℝ} {a : ℕ → ℝ} {C : ℝ}
    (ha : Tendsto a atTop (𝓝 0))
    (hnum : ∀ n ω, |Shat n ω - targetSurvival h₀ F (ξhat n ω) t| ≤ C * a n) :
    TendstoInMeasure P Shat atTop fun _ => targetSurvival h₀ F ξ t := by
  have hc := ((continuous_popSurvival_linearRelativeHazard hloc hnn F).1 t ht).continuousAt
    (x := ξ)
  have hest : TendstoInMeasure P (fun n ω => targetSurvival h₀ F (ξhat n ω) t) atTop
      fun _ => targetSurvival h₀ F ξ t := hξ.comp_continuousAt hc
  have hCa : TendstoInMeasure P (fun n (_ : Ω) => |C * a n|) atTop 0 := by
    refine tendstoInMeasure_of_tendsto_ae (fun _ => aestronglyMeasurable_const)
      (ae_of_all _ fun _ => ?_)
    simpa using (ha.const_mul C).abs
  have hnum' : TendstoInMeasure P
      (fun n ω => Shat n ω - targetSurvival h₀ F (ξhat n ω) t) atTop 0 :=
    hCa.of_norm_le (Eventually.of_forall fun n ω => by
      rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_abs]
      exact (hnum n ω).trans (le_abs_self _))
  have hsum := hnum'.add hest
  simp only [zero_add] at hsum
  exact TendstoInMeasure.congr_left (fun n => ae_of_all _ fun ω => by simp) hsum

/-- **Instance: a unit baseline, a two valued covariate.** With `h₀ = 1`, the covariate law
putting mass `1/2` at `0` and at `1`, and `t = 1`: `∫ Σⱼ |xⱼ| dF = 1/2`, and the estimation
error at the parameters `ξ = (0, log 2)` and `ξ' = (1/10, log 2)` is at most
`(3/2) e^{-1} / 10`, the rate bound of `abs_targetSurvival_sub_le` with `‖ξ' - ξ‖ = 1/10`. -/
theorem targetSurvival_error_instance :
    ∫ x, ∑ j, |x j| ∂twoAtomLaw ![(0 : ℝ)] ![1] (1 / 2) = 1 / 2 ∧
      |targetSurvival (fun _ => 1) (twoAtomLaw ![0] ![1] (1 / 2)) (1 / 10, ![Real.log 2]) 1 -
          targetSurvival (fun _ => 1) (twoAtomLaw ![0] ![1] (1 / 2)) (0, ![Real.log 2]) 1| ≤
        Real.exp (-1) * (3 / 2) * (1 / 10) := by
  have := isProbabilityMeasure_twoAtomLaw (x₁ := ![(0 : ℝ)]) (x₂ := ![1]) (t := 1 / 2)
    (by norm_num) (by norm_num)
  have hI : ∫ x, ∑ j, |x j| ∂twoAtomLaw ![(0 : ℝ)] ![1] (1 / 2) = 1 / 2 := by
    rw [integral_twoAtomLaw (by norm_num) (by norm_num)]
    simp
  refine ⟨hI, ?_⟩
  have hH : 0 ≤ cumHazard (fun _ : ℝ => (1 : ℝ)) 1 := by simp [cumHazard]
  have h := abs_targetSurvival_sub_le hH (twoAtomLaw ![0] ![1] (1 / 2))
    (integrable_twoAtomLaw _) (0, ![Real.log 2]) (1 / 10, ![Real.log 2])
  have hn : ‖((1 / 10 : ℝ), ![Real.log 2]) - (0, ![Real.log 2])‖ = 1 / 10 := by
    rw [Prod.norm_def]
    simp only [Prod.fst_sub, Prod.snd_sub, sub_zero, sub_self, norm_zero]
    norm_num
  rw [hI, hn] at h
  convert h using 2
  norm_num

/-- **Instance: consistency and the rate along a deterministic sequence.** With `h₀ = 1`, the
two valued covariate law, `t = 1`, the estimated parameters `ξ̂ₙ = (1/(n+1), log 2)` and the
computed survivals `Ŝₙ = S(ξ̂ₙ, 1) + 1/(n+1)` (a numerical error `1/(n+1)`): `Ŝₙ → S((0, log 2), 1)`
in probability under the point mass on a one point space, and
`|Ŝₙ - S((0, log 2), 1)| ≤ (1 + (3/2) e^{-1}) / (n+1)`. -/
theorem targetSurvival_consistency_instance :
    TendstoInMeasure (Measure.dirac ())
        (fun (n : ℕ) (_ : Unit) => targetSurvival (fun _ => 1) (twoAtomLaw ![0] ![1] (1 / 2))
          (1 / ((n : ℝ) + 1), ![Real.log 2]) 1 + 1 / ((n : ℝ) + 1)) atTop
        (fun _ => targetSurvival (fun _ => 1) (twoAtomLaw ![0] ![1] (1 / 2))
          (0, ![Real.log 2]) 1) ∧
      ∀ n : ℕ, |targetSurvival (fun _ => 1) (twoAtomLaw ![0] ![1] (1 / 2))
          (1 / ((n : ℝ) + 1), ![Real.log 2]) 1 + 1 / ((n : ℝ) + 1) -
          targetSurvival (fun _ => 1) (twoAtomLaw ![0] ![1] (1 / 2)) (0, ![Real.log 2]) 1| ≤
        (1 + 3 / 2 * Real.exp (-1)) / ((n : ℝ) + 1) := by
  have := isProbabilityMeasure_twoAtomLaw (x₁ := ![(0 : ℝ)]) (x₂ := ![1]) (t := 1 / 2)
    (by norm_num) (by norm_num)
  have hI : ∫ x, ∑ j, |x j| ∂twoAtomLaw ![(0 : ℝ)] ![1] (1 / 2) = 1 / 2 :=
    targetSurvival_error_instance.1
  have hn : ∀ n : ℕ, ‖((1 / ((n : ℝ) + 1) : ℝ), ![Real.log 2]) - (0, ![Real.log 2])‖ =
      1 / ((n : ℝ) + 1) := fun n => by
    rw [Prod.norm_def]
    simp only [Prod.fst_sub, Prod.snd_sub, sub_zero, sub_self, norm_zero]
    rw [Real.norm_eq_abs, abs_of_pos (by positivity), max_eq_left (by positivity)]
  have hlim : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hξ : TendstoInMeasure (Measure.dirac ())
      (fun (n : ℕ) (_ : Unit) => ((1 / ((n : ℝ) + 1) : ℝ), ![Real.log 2])) atTop
      (fun _ => ((0 : ℝ), ![Real.log 2])) := by
    exact tendstoInMeasure_of_tendsto_ae (μ := Measure.dirac ())
      (f := fun (n : ℕ) (_ : Unit) => ((1 / ((n : ℝ) + 1) : ℝ), (![Real.log 2] : Fin 1 → ℝ)))
      (g := fun _ => ((0 : ℝ), (![Real.log 2] : Fin 1 → ℝ)))
      (fun _ => aestronglyMeasurable_const) (ae_of_all _ fun _ =>
        hlim.prodMk_nhds (tendsto_const_nhds (x := (![Real.log 2] : Fin 1 → ℝ))))
  have hH : 0 ≤ cumHazard (fun _ : ℝ => (1 : ℝ)) 1 := by simp [cumHazard]
  refine ⟨tendstoInMeasure_targetSurvival (P := Measure.dirac ())
    (fun a b => intervalIntegrable_const) (fun _ _ => zero_le_one)
    (twoAtomLaw ![0] ![1] (1 / 2)) zero_le_one hξ (C := 1) hlim fun n _ => ?_, fun n => ?_⟩
  · simp only [add_sub_cancel_left, one_mul]
    rw [abs_of_pos (by positivity)]
  · have h := abs_targetSurvival_error_le hH (twoAtomLaw ![0] ![1] (1 / 2))
      (integrable_twoAtomLaw _) (ξ := (0, ![Real.log 2]))
      (ξhat := (1 / ((n : ℝ) + 1), ![Real.log 2]))
      (Shat := targetSurvival (fun _ => 1) (twoAtomLaw ![0] ![1] (1 / 2))
        (1 / ((n : ℝ) + 1), ![Real.log 2]) 1 + 1 / ((n : ℝ) + 1))
      (εnum := 1 / ((n : ℝ) + 1)) (r := 1 / ((n : ℝ) + 1))
      (by rw [add_sub_cancel_left, abs_of_pos (by positivity)]) (hn n).le
    rw [hI] at h
    refine h.trans (le_of_eq ?_)
    ring

end NetworkMetaRegression

end CausalInference
