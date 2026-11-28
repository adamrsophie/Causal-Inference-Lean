/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.NetworkMetaRegression.Model
public import CausalInference.Survival.PopulationHazard
public import CausalInference.Survival.RestrictedMeanCollapsible
public import Mathlib.Probability.Moments.MGFAnalytic
public import Mathlib.Analysis.Analytic.Uniqueness

/-!
# The target survival curve of a multilevel proportional hazards model

**Time scale: continuous.** In a multilevel model for time to event outcomes the conditional
hazard of an arm with cell intercept `c` and cell slope `b` is `h₀(t) exp(c + xᵀb)`, so the
conditional survival curve is `phSurvival (cumHazard h₀) (linearRelativeHazard c b)`:
`S(t | x) = exp(-exp(c + xᵀb) H₀(t))`. The **target survival curve** is the population curve
`popSurvival ν S` of these conditional curves under the covariate law `ν` of the target
population, the integral of the conditional curves.

The library already gives the general facts used here: the population curve of a family of
survival curves is a survival curve (`isSurvivalCurve_popSurvival`), the restricted mean of the
population curve is the average conditional restricted mean, and the difference of two restricted
means is the integral of the conditional differences (`restrictedMean_popSurvival_sub`), and the
population hazard has the survivor weighted form (`popHazard_phSurvival_cumHazard`). This file
adds:

* the bridge from the multilevel model: the conditional curves of arm `k` at the baseline of
  study `j` are the curves of the cell intercept and the cell slope
  (`hazardCurves_eta_mul_eq`);
* continuity of the target curve and of its restricted mean in the parameters, for a general
  parametric family (`continuous_popSurvival_param`, `continuous_restrictedMean_popSurvival_param`)
  and for the proportional hazards family (`continuous_popSurvival_linearRelativeHazard`);
* **non transportability of the restricted mean contrast**: with a common conditional hazard
  ratio `exp(c_A - c_B) ≠ 1` and a slope `b ≠ 0`, the conditional restricted mean contrast is not
  constant on any set of covariates whose predictor `xᵀb` fills an interval, so two target laws
  on such a set have different marginal contrasts
  (`restrictedMeanContrast_not_const_of_interval`, `exists_restrictedMean_popSurvival_sub_ne`);
* a concrete instance with a constant baseline hazard and a two valued covariate in which the
  two marginal contrasts differ at every horizon except one, where they coincide
  (`restrictedMean_contrast_instance`): checking a single horizon does not test transportability.

## Main definitions

* `linearRelativeHazard c b x = exp(c + xᵀb)`.
* `restrictedMeanContrast h₀ cA cB b τ x`, the conditional restricted mean contrast.

## Main results

* `isSurvivalFamily_linearRelativeHazard`, `hazardCurves_eta_mul_eq`.
* `continuous_popSurvival_param`, `continuous_restrictedMean_popSurvival_param`,
  `continuous_popSurvival_linearRelativeHazard`.
* `restrictedMeanContrast_not_const_of_interval`, `exists_restrictedMean_popSurvival_sub_ne`,
  `restrictedMeanContrast_not_const`.
* `restrictedMean_contrast_instance`.

## References

* D. R. Cox, *Regression models and life-tables*, Journal of the Royal Statistical Society
  Series B 34 (1972).
* D. M. Phillippo, S. Dias, A. E. Ades, M. Belger, A. Brnabic, A. Schacht, D. Saure, Z. Kadziola
  and N. J. Welton, *Multilevel network meta-regression for population-adjusted treatment
  comparisons*, Journal of the Royal Statistical Society Series A 183 (2020).
-/

@[expose] public section

namespace CausalInference

namespace NetworkMetaRegression

open MeasureTheory ProbabilityTheory Filter Topology Set
open Survival.ContinuousTime

variable {p : ℕ}

/-! ### The proportional hazards family of a linear predictor -/

/-- The **relative hazard** `exp(c + xᵀb)` of the linear predictor with intercept `c` and slope
`b`. -/
noncomputable def linearRelativeHazard (c : ℝ) (b : Fin p → ℝ) (x : Fin p → ℝ) : ℝ :=
  Real.exp (c + x ⬝ᵥ b)

theorem linearRelativeHazard_pos (c : ℝ) (b x : Fin p → ℝ) : 0 < linearRelativeHazard c b x :=
  Real.exp_pos _

theorem continuous_linearRelativeHazard_param (x : Fin p → ℝ) :
    Continuous fun ξ : ℝ × (Fin p → ℝ) => linearRelativeHazard ξ.1 ξ.2 x := by
  unfold linearRelativeHazard dotProduct
  fun_prop

theorem continuous_linearRelativeHazard (c : ℝ) (b : Fin p → ℝ) :
    Continuous (linearRelativeHazard c b) := by
  unfold linearRelativeHazard dotProduct
  fun_prop

/-- A locally integrable baseline hazard has a continuous cumulative hazard. -/
theorem continuous_cumHazard {h₀ : ℝ → ℝ} (hloc : ∀ a b, IntervalIntegrable h₀ volume a b) :
    Continuous (cumHazard h₀) :=
  intervalIntegral.continuous_primitive hloc 0

/-- **The proportional hazards curves form a family of survival curves** for a locally
integrable baseline hazard that is nonnegative at nonnegative times. -/
theorem isSurvivalFamily_linearRelativeHazard {h₀ : ℝ → ℝ}
    (hloc : ∀ a b, IntervalIntegrable h₀ volume a b) (hnn : ∀ u, 0 ≤ u → 0 ≤ h₀ u) (c : ℝ)
    (b : Fin p → ℝ) :
    IsSurvivalFamily (phSurvival (cumHazard h₀) (linearRelativeHazard c b)) :=
  Survival.ContinuousTime.isSurvivalFamily_phSurvival
    (continuous_linearRelativeHazard c b).measurable
    (fun x => (linearRelativeHazard_pos c b x).le) (continuous_cumHazard hloc).measurable
    fun _ hs => cumHazard_nonneg hnn hs

/-- **The bridge from the multilevel model.** The conditional curves of the hazards
`exp(η_{jk}(x)) h₀(u)` of arm `k` at the baseline of study `j` are the proportional hazards
curves of the cell intercept `μ_j + γ_k` and the cell slope `β₁ + β₂,k`. -/
theorem hazardCurves_eta_mul_eq {J K : Type*} (M : MultilevelModel J K p) (j : J) (k : K)
    (h₀ : ℝ → ℝ) :
    hazardCurves (fun x u => Real.exp (M.eta (M.μ j) k x) * h₀ u) =
      phSurvival (cumHazard h₀) (linearRelativeHazard (M.μ j + M.γ k) (M.β₁ + M.β₂ k)) := by
  rw [show (fun x u => Real.exp (M.eta (M.μ j) k x) * h₀ u) =
      fun x u => linearRelativeHazard (M.μ j + M.γ k) (M.β₁ + M.β₂ k) x * h₀ u by
    funext x u
    rw [linearRelativeHazard, MultilevelModel.eta_eq_affine], hazardCurves_mul]

/-! ### Continuity in the parameters -/

section Continuity

variable {Ξ 𝒳 : Type*} [TopologicalSpace Ξ] [FirstCountableTopology Ξ] [MeasurableSpace 𝒳]

/-- **The target survival curve is continuous in the parameters.** For a parametric family of
conditional survival curves `S ξ`, each a family of survival curves and continuous in `ξ` at every
covariate value and time, the target curve `ξ ↦ ∫ S ξ x t dν(x)` is continuous at every time
`t ≥ 0`, for a finite covariate law `ν`. -/
theorem continuous_popSurvival_param {S : Ξ → 𝒳 → ℝ → ℝ} (hS : ∀ ξ, IsSurvivalFamily (S ξ))
    (hc : ∀ x t, Continuous fun ξ => S ξ x t) (ν : Measure 𝒳) [IsFiniteMeasure ν] {t : ℝ}
    (ht : 0 ≤ t) : Continuous fun ξ => popSurvival ν (S ξ) t :=
  continuous_of_dominated (bound := fun _ => 1)
    (fun ξ => ((hS ξ).integrable ν ht).aestronglyMeasurable)
    (fun ξ => Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg ((hS ξ).nonneg x t ht)]
      exact (hS ξ).le_one x t ht)
    (integrable_const _) (Eventually.of_forall fun x => hc x t)

/-- **The restricted mean of the target curve is continuous in the parameters**, at every horizon
`τ ≥ 0`, under the hypotheses of `continuous_popSurvival_param` with a probability law. -/
theorem continuous_restrictedMean_popSurvival_param {S : Ξ → 𝒳 → ℝ → ℝ}
    (hS : ∀ ξ, IsSurvivalFamily (S ξ)) (hc : ∀ x t, Continuous fun ξ => S ξ x t)
    (ν : Measure 𝒳) [IsProbabilityMeasure ν] {τ : ℝ} (hτ : 0 ≤ τ) :
    Continuous fun ξ => restrictedMean (popSurvival ν (S ξ)) τ := by
  unfold restrictedMean
  refine intervalIntegral.continuous_of_dominated_interval (bound := fun _ => 1)
    (fun ξ => (measurable_popSurvival (hS ξ).measurable ν).aestronglyMeasurable)
    (fun ξ => Eventually.of_forall fun s hs => ?_) intervalIntegrable_const
    (Eventually.of_forall fun s hs => ?_)
  · rw [uIoc_of_le hτ] at hs
    have h := isSurvivalCurve_popSurvival (hS ξ) ν
    rw [Real.norm_eq_abs, abs_of_nonneg (h.nonneg s hs.1.le)]
    exact h.le_one s hs.1.le
  · rw [uIoc_of_le hτ] at hs
    exact continuous_popSurvival_param hS hc ν hs.1.le

/-- **The proportional hazards target curve is continuous in `(c, b)`.** For a locally
integrable baseline hazard, nonnegative at nonnegative times, and a covariate probability law,
the target curve `ξ ↦ ∫ exp(-exp(ξ.1 + xᵀξ.2) H₀(t)) dν(x)` at every `t ≥ 0` and its restricted
mean at every `τ ≥ 0` are continuous in the intercept and slope `ξ`. -/
theorem continuous_popSurvival_linearRelativeHazard {h₀ : ℝ → ℝ}
    (hloc : ∀ a b, IntervalIntegrable h₀ volume a b) (hnn : ∀ u, 0 ≤ u → 0 ≤ h₀ u)
    (ν : Measure (Fin p → ℝ)) [IsProbabilityMeasure ν] :
    (∀ t, 0 ≤ t → Continuous fun ξ : ℝ × (Fin p → ℝ) =>
      popSurvival ν (phSurvival (cumHazard h₀) (linearRelativeHazard ξ.1 ξ.2)) t) ∧
    ∀ τ, 0 ≤ τ → Continuous fun ξ : ℝ × (Fin p → ℝ) =>
      restrictedMean (popSurvival ν (phSurvival (cumHazard h₀) (linearRelativeHazard ξ.1 ξ.2)))
        τ := by
  have hS : ∀ ξ : ℝ × (Fin p → ℝ),
      IsSurvivalFamily (phSurvival (cumHazard h₀) (linearRelativeHazard ξ.1 ξ.2)) := fun ξ =>
    isSurvivalFamily_linearRelativeHazard hloc hnn ξ.1 ξ.2
  have hc : ∀ x t, Continuous fun ξ : ℝ × (Fin p → ℝ) =>
      phSurvival (cumHazard h₀) (linearRelativeHazard ξ.1 ξ.2) x t := fun x t => by
    unfold phSurvival
    have := continuous_linearRelativeHazard_param (p := p) x
    fun_prop
  exact ⟨fun t ht => continuous_popSurvival_param hS hc ν ht,
    fun τ hτ => continuous_restrictedMean_popSurvival_param hS hc ν hτ⟩

end Continuity

/-! ### Non transportability of the restricted mean contrast -/

section NotTransportable

/-- The **conditional restricted mean contrast** `RMST_A(τ | x) - RMST_B(τ | x)` of two arms with
intercepts `cA`, `cB` and a common slope `b`. -/
noncomputable def restrictedMeanContrast (h₀ : ℝ → ℝ) (cA cB : ℝ) (b : Fin p → ℝ) (τ : ℝ)
    (x : Fin p → ℝ) : ℝ :=
  restrictedMean (phSurvival (cumHazard h₀) (linearRelativeHazard cA b) x) τ -
    restrictedMean (phSurvival (cumHazard h₀) (linearRelativeHazard cB b) x) τ

/-- `|e^{-x} - e^{-y}| ≤ |x - y|` for `x, y ≥ 0`. -/
theorem abs_exp_neg_sub_exp_neg_le {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    |Real.exp (-x) - Real.exp (-y)| ≤ |x - y| := by
  wlog hxy : x ≤ y generalizing x y
  · rw [abs_sub_comm, abs_sub_comm x y]; exact this hy hx (le_of_not_ge hxy)
  have e : Real.exp (-y) = Real.exp (-x) * Real.exp (-(y - x)) := by
    rw [← Real.exp_add]; ring_nf
  have h1 := Real.add_one_le_exp (-(y - x))
  have h2 : Real.exp (-(y - x)) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
  have h3 : Real.exp (-x) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
  have h4 := Real.exp_pos (-x)
  rw [abs_of_nonneg (by rw [e]; nlinarith), abs_of_nonpos (by linarith), e]
  nlinarith

/-- **The conditional restricted mean contrast is not constant on an interval.** Let the
baseline hazard be locally integrable and positive at positive times, let the intercepts differ,
`cA ≠ cB`, and `τ > 0`. If the predictor `xᵀb` takes every value of a nondegenerate interval
`(l, r)` as `x` ranges over a set `𝒳` of covariates, the conditional contrast is not constant on
`𝒳`. The conditional hazard ratio `exp(cA - cB)` is the same at every covariate value. The proof
writes the contrast as `D(xᵀb)` with `D(s) = G(e^{cA + s}) - G(e^{cB + s})` and
`G(λ) = ∫₀^τ exp(-λ H₀)`, a moment generating function under Lebesgue measure on `(0, τ]`, hence
analytic; a constant value near an interior point would make `D` constant, but `D(s) → 0` as
`s → -∞` while `D` never vanishes. -/
theorem restrictedMeanContrast_not_const_of_interval {h₀ : ℝ → ℝ}
    (hloc : ∀ a b, IntervalIntegrable h₀ volume a b) (hpos : ∀ s, 0 < s → 0 < h₀ s)
    {cA cB : ℝ} (hc : cA ≠ cB) {b : Fin p → ℝ} {τ : ℝ} (hτ : 0 < τ)
    {𝒳 : Set (Fin p → ℝ)} {l r : ℝ} (hlr : l < r)
    (hrange : ∀ s ∈ Ioo l r, ∃ x ∈ 𝒳, x ⬝ᵥ b = s) :
    ∃ x ∈ 𝒳, ∃ x' ∈ 𝒳,
      restrictedMeanContrast h₀ cA cB b τ x ≠ restrictedMeanContrast h₀ cA cB b τ x' := by
  set H := cumHazard h₀ with hHdef
  have hcH : Continuous H := continuous_cumHazard hloc
  have hHpos : ∀ s, 0 < s → 0 < H s := fun s hs =>
    intervalIntegral.intervalIntegral_pos_of_pos_on (hloc 0 s) (fun u hu => hpos u hu.1) hs
  have hHmono : ∀ s ∈ Ioc 0 τ, 0 ≤ H s ∧ H s ≤ H τ := by
    intro s hs
    refine ⟨(hHpos s hs.1).le, ?_⟩
    rcases hs.2.lt_or_eq with h | h
    · have hd := intervalIntegral.integral_interval_sub_left (hloc 0 τ) (hloc 0 s)
      have h2 : 0 < ∫ u in s..τ, h₀ u :=
        intervalIntegral.intervalIntegral_pos_of_pos_on (hloc s τ)
          (fun u hu => hpos u (hs.1.trans hu.1)) h
      simp only [hHdef, cumHazard] at hd ⊢
      linarith
    · rw [h]
  set μ : Measure ℝ := volume.restrict (Ioc 0 τ) with hμ
  -- `G` is a moment generating function
  set G : ℝ → ℝ := mgf (fun s => -H s) μ with hG
  have hGint : ∀ l : ℝ, G l = ∫ s in (0 : ℝ)..τ, Real.exp (-(l * H s)) := fun l => by
    rw [hG, mgf, intervalIntegral.integral_of_le hτ.le]
    congr 1
    funext s
    ring_nf
  have hexpset : integrableExpSet (fun s => -H s) μ = univ := by
    refine eq_univ_of_forall fun l => ?_
    exact ((show Continuous fun s => Real.exp (l * -H s) by fun_prop).integrableOn_Icc).mono_set
      Ioc_subset_Icc_self
  have hGan : AnalyticOnNhd ℝ G univ := by
    have := analyticOnNhd_mgf (X := fun s => -H s) (μ := μ)
    rwa [hexpset, interior_univ] at this
  set D : ℝ → ℝ := fun s => G (Real.exp (cA + s)) - G (Real.exp (cB + s)) with hD
  have hDan : AnalyticOnNhd ℝ D univ := fun s _ =>
    ((hGan _ (mem_univ _)).comp (analyticAt_const.add analyticAt_id).rexp).sub
      ((hGan _ (mem_univ _)).comp (analyticAt_const.add analyticAt_id).rexp)
  have hΔD : ∀ x, restrictedMeanContrast h₀ cA cB b τ x = D (x ⬝ᵥ b) := fun x => by
    simp only [restrictedMeanContrast, hD, hGint, restrictedMean, phSurvival,
      linearRelativeHazard, hHdef]
  have hcE : ∀ c : ℝ, Continuous fun s => Real.exp (-(c * H s)) := fun c => by fun_prop
  have hDint : ∀ s, D s = ∫ u in (0 : ℝ)..τ, (Real.exp (-(Real.exp (cA + s) * H u)) -
      Real.exp (-(Real.exp (cB + s) * H u))) := fun s => by
    simp only [hD, hGint]
    rw [intervalIntegral.integral_sub ((hcE _).intervalIntegrable 0 τ)
      ((hcE _).intervalIntegrable 0 τ)]
  -- `D` never vanishes
  have hDne : ∀ s, D s ≠ 0 := fun s => by
    have hne : Real.exp (cA + s) ≠ Real.exp (cB + s) := fun h =>
      hc (by have := Real.exp_injective h; linarith)
    rw [hDint]
    have hint : IntervalIntegrable (fun u => Real.exp (-(Real.exp (cA + s) * H u)) -
        Real.exp (-(Real.exp (cB + s) * H u))) volume 0 τ :=
      ((hcE _).sub (hcE _)).intervalIntegrable 0 τ
    rcases lt_or_gt_of_ne hne with h | h
    · refine (intervalIntegral.intervalIntegral_pos_of_pos_on hint (fun u hu => ?_) hτ).ne'
      have := hHpos u hu.1
      rw [sub_pos, Real.exp_lt_exp]
      nlinarith
    · refine (neg_pos.1 ?_).ne
      rw [← intervalIntegral.integral_neg]
      refine intervalIntegral.intervalIntegral_pos_of_pos_on hint.neg (fun u hu => ?_) hτ
      have := hHpos u hu.1
      rw [neg_pos, sub_neg, Real.exp_lt_exp]
      nlinarith
  -- `D(s) → 0` as `s → -∞`
  have hHτ : 0 ≤ H τ := (hHpos τ hτ).le
  have hbound : ∀ s, |D s| ≤ Real.exp s * (|Real.exp cA - Real.exp cB| * H τ * τ) := by
    intro s
    rw [hDint, ← Real.norm_eq_abs]
    have := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := τ)
      (C := |Real.exp cA - Real.exp cB| * Real.exp s * H τ)
      (f := fun u => Real.exp (-(Real.exp (cA + s) * H u)) -
        Real.exp (-(Real.exp (cB + s) * H u))) (fun u hu => by
          rw [uIoc_of_le hτ.le] at hu
          obtain ⟨hu0, hule⟩ := hHmono u hu
          rw [Real.norm_eq_abs]
          refine (abs_exp_neg_sub_exp_neg_le (by positivity) (by positivity)).trans ?_
          rw [Real.exp_add, Real.exp_add, show Real.exp cA * Real.exp s * H u -
              Real.exp cB * Real.exp s * H u =
            (Real.exp cA - Real.exp cB) * (Real.exp s * H u) by ring, abs_mul,
            abs_of_nonneg (by positivity : 0 ≤ Real.exp s * H u), mul_assoc]
          exact mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left hule (Real.exp_pos _).le) (abs_nonneg _))
    refine this.trans (le_of_eq ?_)
    rw [sub_zero, abs_of_pos hτ]
    ring
  have hlim : Tendsto D atBot (𝓝 0) := by
    have h0 := Real.tendsto_exp_atBot.mul_const (|Real.exp cA - Real.exp cB| * H τ * τ)
    rw [zero_mul] at h0
    exact squeeze_zero_norm hbound h0
  -- conclusion
  by_contra hcon
  push Not at hcon
  have hm : (l + r) / 2 ∈ Ioo l r := ⟨by linarith, by linarith⟩
  have hconst : ∀ s ∈ Ioo l r, D s = D ((l + r) / 2) := fun s hs => by
    obtain ⟨x, hx, hxs⟩ := hrange s hs
    obtain ⟨x', hx', hxs'⟩ := hrange ((l + r) / 2) hm
    rw [← hxs, ← hxs', ← hΔD, ← hΔD]
    exact hcon x hx x' hx'
  have hev : D =ᶠ[𝓝 ((l + r) / 2)] fun _ => D ((l + r) / 2) :=
    eventually_of_mem (Ioo_mem_nhds hm.1 hm.2) hconst
  have heq := AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq hDan analyticOnNhd_const
    isPreconnected_univ (mem_univ _) hev
  have hlim' : Tendsto D atBot (𝓝 (D ((l + r) / 2))) :=
    tendsto_const_nhds.congr fun s => (heq (mem_univ s)).symm
  exact hDne _ (tendsto_nhds_unique hlim' hlim)

/-- With a nonzero slope the predictor `xᵀb` takes every real value. -/
theorem exists_dotProduct_eq {b : Fin p → ℝ} (hb : b ≠ 0) (s : ℝ) :
    ∃ x : Fin p → ℝ, x ⬝ᵥ b = s := by
  have hb2 : 0 < b ⬝ᵥ b := by
    obtain ⟨j, hj⟩ := Function.ne_iff.1 hb
    simp only [dotProduct]
    exact lt_of_lt_of_le (mul_self_pos.2 hj)
      (Finset.single_le_sum (f := fun i => b i * b i) (fun i _ => mul_self_nonneg (b i))
        (Finset.mem_univ j))
  exact ⟨(s / (b ⬝ᵥ b)) • b, by rw [smul_dotProduct, smul_eq_mul, div_mul_cancel₀ s hb2.ne']⟩

/-- **The restricted mean contrast is not transportable.** Under the hypotheses of
`restrictedMeanContrast_not_const_of_interval`, there are two target populations, the point
masses at two covariate values in `𝒳`, whose marginal restricted mean contrasts
`RMST(τ; popSurvival ν S_A) - RMST(τ; popSurvival ν S_B)` differ, although the conditional hazard
ratio `exp(cA - cB)` is the same in every population. With a nonzero slope `𝒳` may be the whole
covariate space. -/
theorem exists_restrictedMean_popSurvival_sub_ne {h₀ : ℝ → ℝ}
    (hloc : ∀ a b, IntervalIntegrable h₀ volume a b) (hpos : ∀ s, 0 < s → 0 < h₀ s)
    {cA cB : ℝ} (hc : cA ≠ cB) {b : Fin p → ℝ} {τ : ℝ} (hτ : 0 < τ)
    {𝒳 : Set (Fin p → ℝ)} {l r : ℝ} (hlr : l < r)
    (hrange : ∀ s ∈ Ioo l r, ∃ x ∈ 𝒳, x ⬝ᵥ b = s) :
    ∃ x ∈ 𝒳, ∃ x' ∈ 𝒳,
      restrictedMean (popSurvival (Measure.dirac x) (phSurvival (cumHazard h₀)
          (linearRelativeHazard cA b))) τ -
        restrictedMean (popSurvival (Measure.dirac x) (phSurvival (cumHazard h₀)
          (linearRelativeHazard cB b))) τ ≠
      restrictedMean (popSurvival (Measure.dirac x') (phSurvival (cumHazard h₀)
          (linearRelativeHazard cA b))) τ -
        restrictedMean (popSurvival (Measure.dirac x') (phSurvival (cumHazard h₀)
          (linearRelativeHazard cB b))) τ := by
  obtain ⟨x, hx, x', hx', hne⟩ :=
    restrictedMeanContrast_not_const_of_interval hloc hpos hc hτ hlr hrange
  exact ⟨x, hx, x', hx', by simpa only [popSurvival_dirac, restrictedMeanContrast] using hne⟩

/-- **The point form**: with a nonzero slope, the conditional restricted mean contrast takes two
different values. -/
theorem restrictedMeanContrast_not_const {h₀ : ℝ → ℝ}
    (hloc : ∀ a b, IntervalIntegrable h₀ volume a b) (hpos : ∀ s, 0 < s → 0 < h₀ s)
    {cA cB : ℝ} (hc : cA ≠ cB) {b : Fin p → ℝ} (hb : b ≠ 0) {τ : ℝ} (hτ : 0 < τ) :
    ∃ x x' : Fin p → ℝ,
      restrictedMeanContrast h₀ cA cB b τ x ≠ restrictedMeanContrast h₀ cA cB b τ x' := by
  obtain ⟨x, -, x', -, h⟩ := restrictedMeanContrast_not_const_of_interval (𝒳 := univ) hloc hpos
    hc hτ zero_lt_one fun s _ => by
      obtain ⟨x, hx⟩ := exists_dotProduct_eq hb s
      exact ⟨x, mem_univ x, hx⟩
  exact ⟨x, x', h⟩

/-! ### A concrete instance -/

/-- The proportional hazards curve of the constant baseline hazard `1` is `exp(-(ρ x s))`. -/
theorem phSurvival_cumHazard_one (ρ : (Fin p → ℝ) → ℝ) (x : Fin p → ℝ) :
    phSurvival (cumHazard fun _ => (1 : ℝ)) ρ x = fun s => Real.exp (-(ρ x * s)) := by
  funext s
  simp [phSurvival, cumHazard]

/-- The marginal restricted mean contrast under a point mass for the instance. -/
theorem restrictedMean_contrast_dirac_one (cA cB : ℝ) (b x : Fin p → ℝ) (τ : ℝ) :
    restrictedMean (popSurvival (Measure.dirac x) (phSurvival (cumHazard fun _ => (1 : ℝ))
        (linearRelativeHazard cA b))) τ -
      restrictedMean (popSurvival (Measure.dirac x) (phSurvival (cumHazard fun _ => (1 : ℝ))
        (linearRelativeHazard cB b))) τ =
    (1 - Real.exp (-(linearRelativeHazard cA b x * τ))) / linearRelativeHazard cA b x -
      (1 - Real.exp (-(linearRelativeHazard cB b x * τ))) / linearRelativeHazard cB b x := by
  rw [popSurvival_dirac, popSurvival_dirac, phSurvival_cumHazard_one, phSurvival_cumHazard_one,
    restrictedMean_exp_mul (linearRelativeHazard_pos _ _ _).ne',
    restrictedMean_exp_mul (linearRelativeHazard_pos _ _ _).ne']

/-- **A horizon that hides the non transportability.** Take the constant baseline hazard `1`,
one covariate, intercepts `cA = log 2`, `cB = 0` (conditional hazard ratio `2`) and slope
`log 2`, and the target populations concentrated at the covariate values `0` and `1`. At the
horizon `τ > 0`, with `u = e^{-τ}`, the marginal restricted mean contrasts are `-(1 - u)²/2` and
`-(1 - u²)²/4`. They differ at every horizon `τ > 0` except `τ = log(1 + √2)`, where they
coincide. -/
theorem restrictedMean_contrast_instance {τ : ℝ} (hτ : 0 < τ) :
    let Δ : (Fin 1 → ℝ) → ℝ := fun x =>
      restrictedMean (popSurvival (Measure.dirac x) (phSurvival (cumHazard fun _ => (1 : ℝ))
          (linearRelativeHazard (Real.log 2) ![Real.log 2]))) τ -
        restrictedMean (popSurvival (Measure.dirac x) (phSurvival (cumHazard fun _ => (1 : ℝ))
          (linearRelativeHazard 0 ![Real.log 2]))) τ
    Δ ![0] = -(1 - Real.exp (-τ)) ^ 2 / 2 ∧
      Δ ![1] = -(1 - Real.exp (-τ) ^ 2) ^ 2 / 4 ∧
      (Δ ![0] = Δ ![1] ↔ τ = Real.log (1 + Real.sqrt 2)) := by
  intro Δ
  have l2 : Real.exp (Real.log 2) = 2 := Real.exp_log (by norm_num)
  set u := Real.exp (-τ) with hu
  have hu0 : 0 < u := Real.exp_pos _
  have hu1 : u < 1 := Real.exp_lt_one_iff.2 (by linarith)
  have hu2 : Real.exp (-(2 * τ)) = u ^ 2 := by
    rw [hu, ← Real.exp_nat_mul]; ring_nf
  have hu4 : Real.exp (-(4 * τ)) = u ^ 4 := by
    rw [hu, ← Real.exp_nat_mul]; ring_nf
  have h0 : Δ ![0] = -(1 - u) ^ 2 / 2 := by
    simp only [Δ]
    rw [restrictedMean_contrast_dirac_one]
    simp only [linearRelativeHazard, dotProduct, Finset.univ_unique, Fin.default_eq_zero,
      Fin.isValue, Matrix.cons_val_fin_one, Finset.sum_singleton, zero_mul, add_zero, l2,
      Real.exp_zero, one_mul]
    rw [hu2]
    field_simp
    ring
  have h1 : Δ ![1] = -(1 - u ^ 2) ^ 2 / 4 := by
    simp only [Δ]
    rw [restrictedMean_contrast_dirac_one]
    simp only [linearRelativeHazard, dotProduct, Finset.univ_unique, Fin.default_eq_zero,
      Fin.isValue, Matrix.cons_val_fin_one, Finset.sum_singleton, one_mul, zero_add]
    rw [Real.exp_add, l2, show (2 : ℝ) * 2 = 4 by norm_num, hu2, hu4]
    field_simp
    ring
  refine ⟨h0, h1, ?_⟩
  rw [h0, h1]
  have hs : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hs1 : 1 < Real.sqrt 2 := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  constructor
  · intro h
    have hsq : (1 + u) ^ 2 = 2 := by
      have hne : (1 - u) ^ 2 ≠ 0 := by positivity
      have : (1 - u) ^ 2 * ((1 + u) ^ 2 - 2) = 0 := by nlinarith
      have := (mul_eq_zero.1 this).resolve_left hne
      linarith
    have hu' : u = Real.sqrt 2 - 1 := by nlinarith
    have hτ' : -τ = Real.log (Real.sqrt 2 - 1) := by
      rw [← hu', hu, Real.log_exp]
    have hinv : Real.log (Real.sqrt 2 - 1) = -Real.log (1 + Real.sqrt 2) := by
      rw [← Real.log_inv]
      congr 1
      field_simp
      nlinarith
    linarith
  · intro h
    have hu' : u = Real.sqrt 2 - 1 := by
      rw [hu, h, ← Real.log_inv, Real.exp_log (by positivity)]
      field_simp
      nlinarith
    rw [hu']
    nlinarith

end NotTransportable

end NetworkMetaRegression

end CausalInference
