/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.IndirectComparison.SmallestNetwork

/-!
# Standardization of an outcome model: the two estimands and their continuity

Population adjustment by an outcome model fits the conditional mean `m_t(x)` of the outcome of
each arm in the trial with individual data and standardizes it to the covariate law `ν` of a
target. On the scale `g` the result is the **marginal estimand**

`linkMarginal g ν m_a m_b = g(∫ m_b dν) - g(∫ m_a dν)`

the difference of the link positions `linkPosition g ν m_t`; for a
population `Q` with conditional mean functions `m_t` and integrable potential outcomes it is the
marginal effect of `Q` (`Population.marginalEffect_eq_linkMarginal`). A common shortcut evaluates
the surfaces at the mean covariate vector `x̄ = covMean ν` instead: the **plug-in at the mean
covariates** (`plugInEffect`),

`plugInEffect g ν m_a m_b = g(m_b(x̄)) - g(m_a(x̄))`,

the conditional effect `linkContrast g m_a m_b` at `x̄`. The orientation is that of
`Population.marginalEffect`: the effect of `b` relative to `a`.

**The plug-in depends on the version of the surfaces.** The point `x̄` may carry no mass under
`ν` (under two equally likely strata `±1` it is `0`), so two versions of the same conditional
mean function can give different plug-ins. Results about `plugInEffect` therefore assume the model
equations at every point, not only almost everywhere.

**Continuity.** A fitted surface is plugged into the same functionals. The standardized mean
`∫ m dν` is continuous for convergence of the surfaces in `L¹(ν)`
(`tendsto_integral_of_tendsto_integral_abs_sub`) and for uniform convergence on a set of full
`ν`-measure when `ν` is finite (`tendsto_integral_of_tendstoUniformlyOn`); the marginal estimand
follows when the link is continuous at the limiting arm means (`tendsto_linkMarginal`,
`tendsto_linkMarginal_of_integral_abs_sub`, `tendsto_linkMarginal_of_tendstoUniformlyOn`). The
plug-in needs convergence of the surfaces at the mean covariate itself
(`tendsto_plugInEffect`).

## Main definitions

* `plugInEffect g ν m_a m_b`: the conditional effect at the mean covariates of `ν`.

## Main results

* `linkMarginal_covLaw`, `covMean_covLaw`: the estimands of a population as integrals over its
  sample space.
* `abs_integral_sub_integral_le`, `tendsto_integral_of_tendsto_integral_abs_sub`,
  `tendsto_integral_of_tendstoUniformlyOn`: continuity of the standardized mean.
* `tendsto_linkMarginal`, `tendsto_linkMarginal_of_integral_abs_sub`,
  `tendsto_linkMarginal_of_tendstoUniformlyOn`: continuity of the marginal estimand.
* `tendsto_plugInEffect`: continuity of the plug-in.

## References

* J. J. Caro and K. J. Ishak, *No head-to-head trial? Simulate the missing arms*,
  PharmacoEconomics 28 (2010).
* D. M. Phillippo, A. E. Ades, S. Dias, S. Palmer, K. R. Abrams and N. J. Welton, *Methods for
  population-adjusted indirect comparisons in health technology appraisal*, Medical Decision
  Making 38 (2018).
-/

@[expose] public section

namespace CausalInference

namespace PopulationAdjustment

open MeasureTheory Filter Topology EffectMeasure IndirectComparison

/-! ### The plug-in at the mean covariates -/

section PlugIn

variable {p : ℕ}

/-- The **plug-in effect at the mean covariates** of the covariate law `ν` on `ℝ^p`: the
conditional effect `g(m_b(x̄)) - g(m_a(x̄))` of `b` relative to `a` at `x̄ = covMean ν`. -/
noncomputable def plugInEffect (g : ℝ → ℝ) (ν : Measure (Fin p → ℝ))
    (ma mb : (Fin p → ℝ) → ℝ) : ℝ :=
  linkContrast g ma mb (covMean ν)

/-- The plug-in effect is the difference of the link values of the two surfaces at `x̄`. -/
theorem plugInEffect_eq (g : ℝ → ℝ) (ν : Measure (Fin p → ℝ)) (ma mb : (Fin p → ℝ) → ℝ) :
    plugInEffect g ν ma mb = g (mb (covMean ν)) - g (ma (covMean ν)) := rfl

end PlugIn

/-! ### The estimands of a population -/

section Population

variable {Ω 𝒳 ι : Type*} [MeasurableSpace Ω] [MeasurableSpace 𝒳]

/-- **The marginal estimand of a population over its sample space**: for measurable covariates
and surfaces, `linkMarginal g Q_X m_a m_b = g(E[m_b(X)]) - g(E[m_a(X)])`. -/
theorem linkMarginal_covLaw (g : ℝ → ℝ) {Q : Population Ω 𝒳 ι} (hX : Measurable Q.X)
    {ma mb : 𝒳 → ℝ} (ha : Measurable ma) (hb : Measurable mb) :
    linkMarginal g Q.covLaw ma mb =
      g (∫ ω, mb (Q.X ω) ∂Q.μ) - g (∫ ω, ma (Q.X ω) ∂Q.μ) := by
  rw [linkMarginal, Population.covLaw, integral_map hX.aemeasurable ha.aestronglyMeasurable,
    integral_map hX.aemeasurable hb.aestronglyMeasurable]

/-- The mean covariate vector of a population on `ℝ^p` is the mean of its covariates. -/
theorem covMean_covLaw {p : ℕ} {Q : Population Ω (Fin p → ℝ) ι} (hX : Measurable Q.X)
    (k : Fin p) : covMean Q.covLaw k = ∫ ω, Q.X ω k ∂Q.μ := by
  rw [covMean, Population.covLaw,
    integral_map hX.aemeasurable (measurable_pi_apply k).aestronglyMeasurable]

end Population

/-! ### Continuity of the standardized mean -/

section Continuity

variable {𝒳 : Type*} [MeasurableSpace 𝒳] {ν : Measure 𝒳}

/-- The standardized means of two integrable surfaces differ by at most the `L¹(ν)` distance of
the surfaces: `|∫ m' dν - ∫ m dν| ≤ ∫ |m' - m| dν`. -/
theorem abs_integral_sub_integral_le {m m' : 𝒳 → ℝ} (hm : Integrable m ν)
    (hm' : Integrable m' ν) :
    |∫ x, m' x ∂ν - ∫ x, m x ∂ν| ≤ ∫ x, |m' x - m x| ∂ν := by
  rw [← integral_sub hm' hm]
  exact abs_integral_le_integral_abs

/-- **Continuity of the standardized mean in `L¹`.** If the surfaces `m_n` are eventually
integrable, `m` is integrable and `∫ |m_n - m| dν → 0`, then `∫ m_n dν → ∫ m dν`. -/
theorem tendsto_integral_of_tendsto_integral_abs_sub {α : Type*} {l : Filter α}
    {m : 𝒳 → ℝ} {mn : α → 𝒳 → ℝ} (hm : Integrable m ν)
    (hmn : ∀ᶠ n in l, Integrable (mn n) ν)
    (hL1 : Tendsto (fun n => ∫ x, |mn n x - m x| ∂ν) l (𝓝 0)) :
    Tendsto (fun n => ∫ x, mn n x ∂ν) l (𝓝 (∫ x, m x ∂ν)) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero' (Eventually.of_forall fun n => norm_nonneg _) ?_ hL1
  filter_upwards [hmn] with n hn
  rw [Real.norm_eq_abs]
  exact abs_integral_sub_integral_le hm hn

/-- **Continuity of the standardized mean under uniform convergence on the support.** Let `ν` be
finite and `S` a set of full `ν`-measure. If the surfaces `m_n` are eventually integrable, `m`
is integrable and `m_n → m` uniformly on `S`, then `∫ m_n dν → ∫ m dν`. -/
theorem tendsto_integral_of_tendstoUniformlyOn [IsFiniteMeasure ν] {α : Type*} {l : Filter α}
    {S : Set 𝒳} (hS : ∀ᵐ x ∂ν, x ∈ S) {m : 𝒳 → ℝ} {mn : α → 𝒳 → ℝ} (hm : Integrable m ν)
    (hmn : ∀ᶠ n in l, Integrable (mn n) ν) (hu : TendstoUniformlyOn mn m l S) :
    Tendsto (fun n => ∫ x, mn n x ∂ν) l (𝓝 (∫ x, m x ∂ν)) := by
  refine tendsto_integral_of_tendsto_integral_abs_sub hm hmn ?_
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hε' : 0 < ε / (ν.real Set.univ + 1) := div_pos hε (by positivity)
  filter_upwards [hmn, (Metric.tendstoUniformlyOn_iff.1 hu) _ hε'] with n hn hun
  have hle : ∫ x, |mn n x - m x| ∂ν ≤ ∫ _x, ε / (ν.real Set.univ + 1) ∂ν := by
    refine integral_mono_ae (hn.sub hm).abs (integrable_const _) ?_
    filter_upwards [hS] with x hx
    have := hun x hx
    rw [Real.dist_eq, abs_sub_comm] at this
    exact this.le
  rw [integral_const, smul_eq_mul] at hle
  have h0 : 0 ≤ ∫ x, |mn n x - m x| ∂ν := integral_nonneg fun _ => abs_nonneg _
  rw [Real.dist_eq, sub_zero, abs_of_nonneg h0]
  calc ∫ x, |mn n x - m x| ∂ν ≤ ν.real Set.univ * (ε / (ν.real Set.univ + 1)) := hle
    _ < (ν.real Set.univ + 1) * (ε / (ν.real Set.univ + 1)) := by
        gcongr
        linarith
    _ = ε := by field_simp

/-! ### Continuity of the marginal estimand -/

/-- **Continuity of the marginal estimand.** If the standardized means of the fitted surfaces
converge to those of `m_a` and `m_b`, and the link `g` is continuous at the two limiting arm
means, then the marginal estimands converge. -/
theorem tendsto_linkMarginal {α : Type*} {l : Filter α} {g : ℝ → ℝ} {ma mb : 𝒳 → ℝ}
    {ma' mb' : α → 𝒳 → ℝ}
    (ha : Tendsto (fun n => ∫ x, ma' n x ∂ν) l (𝓝 (∫ x, ma x ∂ν)))
    (hb : Tendsto (fun n => ∫ x, mb' n x ∂ν) l (𝓝 (∫ x, mb x ∂ν)))
    (hga : ContinuousAt g (∫ x, ma x ∂ν)) (hgb : ContinuousAt g (∫ x, mb x ∂ν)) :
    Tendsto (fun n => linkMarginal g ν (ma' n) (mb' n)) l (𝓝 (linkMarginal g ν ma mb)) :=
  (hgb.tendsto.comp hb).sub (hga.tendsto.comp ha)

/-- **Continuity of the marginal estimand in `L¹`**: for integrable surfaces converging in
`L¹(ν)` and a link continuous at the limiting arm means. -/
theorem tendsto_linkMarginal_of_integral_abs_sub {α : Type*} {l : Filter α} {g : ℝ → ℝ}
    {ma mb : 𝒳 → ℝ} {ma' mb' : α → 𝒳 → ℝ} (ha : Integrable ma ν) (hb : Integrable mb ν)
    (ha' : ∀ᶠ n in l, Integrable (ma' n) ν) (hb' : ∀ᶠ n in l, Integrable (mb' n) ν)
    (hLa : Tendsto (fun n => ∫ x, |ma' n x - ma x| ∂ν) l (𝓝 0))
    (hLb : Tendsto (fun n => ∫ x, |mb' n x - mb x| ∂ν) l (𝓝 0))
    (hga : ContinuousAt g (∫ x, ma x ∂ν)) (hgb : ContinuousAt g (∫ x, mb x ∂ν)) :
    Tendsto (fun n => linkMarginal g ν (ma' n) (mb' n)) l (𝓝 (linkMarginal g ν ma mb)) :=
  tendsto_linkMarginal (tendsto_integral_of_tendsto_integral_abs_sub ha ha' hLa)
    (tendsto_integral_of_tendsto_integral_abs_sub hb hb' hLb) hga hgb

/-- **Continuity of the marginal estimand under uniform convergence on the support**: for a
finite `ν`, integrable surfaces converging uniformly on a set of full `ν`-measure, and a link
continuous at the limiting arm means. -/
theorem tendsto_linkMarginal_of_tendstoUniformlyOn [IsFiniteMeasure ν] {α : Type*}
    {l : Filter α} {S : Set 𝒳} (hS : ∀ᵐ x ∂ν, x ∈ S) {g : ℝ → ℝ} {ma mb : 𝒳 → ℝ}
    {ma' mb' : α → 𝒳 → ℝ} (ha : Integrable ma ν) (hb : Integrable mb ν)
    (ha' : ∀ᶠ n in l, Integrable (ma' n) ν) (hb' : ∀ᶠ n in l, Integrable (mb' n) ν)
    (hua : TendstoUniformlyOn ma' ma l S) (hub : TendstoUniformlyOn mb' mb l S)
    (hga : ContinuousAt g (∫ x, ma x ∂ν)) (hgb : ContinuousAt g (∫ x, mb x ∂ν)) :
    Tendsto (fun n => linkMarginal g ν (ma' n) (mb' n)) l (𝓝 (linkMarginal g ν ma mb)) :=
  tendsto_linkMarginal (tendsto_integral_of_tendstoUniformlyOn hS ha ha' hua)
    (tendsto_integral_of_tendstoUniformlyOn hS hb hb' hub) hga hgb

end Continuity

/-! ### Continuity of the plug-in -/

/-- **Continuity of the plug-in at the mean covariates.** If the fitted surfaces converge at the
mean covariate `x̄ = covMean ν` and the link is continuous at `m_a(x̄)` and `m_b(x̄)`, the
plug-in effects converge. Convergence in `L¹(ν)` or on the support of `ν` does not suffice,
since `x̄` may carry no mass. -/
theorem tendsto_plugInEffect {p : ℕ} {α : Type*} {l : Filter α} {g : ℝ → ℝ}
    {ν : Measure (Fin p → ℝ)} {ma mb : (Fin p → ℝ) → ℝ} {ma' mb' : α → (Fin p → ℝ) → ℝ}
    (ha : Tendsto (fun n => ma' n (covMean ν)) l (𝓝 (ma (covMean ν))))
    (hb : Tendsto (fun n => mb' n (covMean ν)) l (𝓝 (mb (covMean ν))))
    (hga : ContinuousAt g (ma (covMean ν))) (hgb : ContinuousAt g (mb (covMean ν))) :
    Tendsto (fun n => plugInEffect g ν (ma' n) (mb' n)) l (𝓝 (plugInEffect g ν ma mb)) :=
  (hgb.tendsto.comp hb).sub (hga.tendsto.comp ha)

end PopulationAdjustment

end CausalInference
