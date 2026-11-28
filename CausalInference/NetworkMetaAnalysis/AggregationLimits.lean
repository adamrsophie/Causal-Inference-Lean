/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.IndirectComparison.AnchoredBias
public import CausalInference.Measures.LinkScaleExamples

/-!
# The limits of aggregate data network meta-analysis on a non collapsible scale

An aggregate data network meta-analysis combines the **marginal** effects that the trials report,
each computed under the trial's own covariate law. Let `m_a, m_b, m_c` be conditional mean
functions common to the trial of `a` against `c` (covariate law `P_ac`), the trial of `b`
against `c` (law `P_bc`) and the target (law `P_*`). The indirect comparison of the reported
marginal effects is `g(m̄_c) - g(m̄_a)` under `P_ac` minus `g(m̄_c) - g(m̄_b)` under `P_bc`
(`marginalIndirectEstimand`); the target is the marginal effect of `b` against `a` under `P_*`.

* **Bias decomposition** (`marginalIndirectEstimand_sub_linkMarginal`): the bias is
  `B_ac - B_bc` with `B_tc` the change of the marginal effect of `c` against `t` between the
  trial's covariate law and the target's.
* **Through the averaging gaps** (`marginalIndirectEstimand_sub_linkMarginal_eq_averagingGap`):
  without effect modification on the conditional scale (both conditional contrasts almost
  surely constant), the bias is a combination of the averaging gaps
  `J_P(m) = g(∫ m dP) - ∫ g ∘ m dP`; nothing of the conditional effects survives.
* **When it vanishes.** On every scale, when the trials share the target's covariate law
  (`marginalIndirectEstimand_self`). On a collapsible scale (the `LinkCollapsible`),
  without effect modification, for all covariate laws
  (`marginalIndirectEstimand_eq_of_linkCollapsible`); in particular on the risk difference scale.
* **When it does not** (`marginalIndirect_logit_bias_example`): on the logit scale, with a
  binary covariate, a constant conditional log odds ratio `-log 4` of `c` against `a`, `b` equal
  to `c`, the trial of `a` at `x = 0` and the target with two equally likely strata, the indirect
  comparison is `log (1/4)`, the target marginal log odds ratio is `log (49/169)`, and the bias
  is `log (169/196) ≠ 0`, with no effect modification at all. The same model shows that the
  marginal log odds ratio depends on the covariate law under a constant conditional one.
* **A binary covariate** (`linkMarginal_bernoulli`, `marginalIndirectEstimand_bernoulli`,
  `anchoredConditional_bias_bernoulli`): with `P(x = 1) = p`, the marginal means are mixtures
  `(1 - p) m(0) + p m(1)` and the bias of the marginal comparison is explicit; the bias of the
  anchored comparison of average conditional effects is `s_ac (p_ac - p_*) - s_bc (p_bc - p_*)`
  with `s_tc = τ_tc(1) - τ_tc(0)`: zero without effect modification or with equal covariate
  laws, and nonzero otherwise.

## Main definitions

* `marginalIndirectEstimand`, `bernoulliLaw`.

## Main results

* `marginalIndirectEstimand_sub_linkMarginal`, `marginalIndirectEstimand_self`,
  `linkMarginal_sub_linkMarginal_eq_averagingGap`,
  `marginalIndirectEstimand_sub_linkMarginal_eq_averagingGap`,
  `marginalIndirectEstimand_eq_of_linkCollapsible`.
* `marginalIndirect_logit_bias_example`.
* `integral_bernoulliLaw`, `linkMarginal_bernoulli`, `marginalIndirectEstimand_bernoulli`,
  `anchoredConditional_bias_bernoulli`, `anchoredConditional_bias_bernoulli_ne_zero`.
* `integral_eq_forall_iff_const`, `anchoredConditional_bias_eq_zero_of_const`,
  `anchoredConditional_exists_bias_ne_zero`, `exists_linkMarginal_ne`.

## References

* H. C. Bucher, G. H. Guyatt, L. E. Griffith and S. D. Walter, *The results of direct and
  indirect treatment comparisons in meta-analysis of randomized controlled trials*, Journal of
  Clinical Epidemiology 50 (1997).
-/

@[expose] public section

namespace CausalInference

namespace NetworkMetaAnalysis

open MeasureTheory EffectMeasure IndirectComparison

/-! ### The indirect comparison of marginal effects -/

section General

variable {𝒳 : Type*} [MeasurableSpace 𝒳]

/-- The **indirect comparison of marginal effects**: the marginal effect of `c` against `a`
under the covariate law `P_ac` of the first trial minus the marginal effect of `c` against `b`
under the covariate law `P_bc` of the second, the aggregate data estimand of the effect of `b`
against `a`. -/
noncomputable def marginalIndirectEstimand (g : ℝ → ℝ) (Pac Pbc : Measure 𝒳) (ma mb mc : 𝒳 → ℝ) :
    ℝ :=
  linkMarginal g Pac ma mc - linkMarginal g Pbc mb mc

/-- **The bias decomposition of the marginal indirect comparison**: its difference from the
target marginal effect is `B_ac - B_bc`, with `B_tc` the change of the marginal effect of `c`
against `t` between the trial's covariate law and the target's. -/
theorem marginalIndirectEstimand_sub_linkMarginal (g : ℝ → ℝ) (Pac Pbc Pt : Measure 𝒳)
    (ma mb mc : 𝒳 → ℝ) :
    marginalIndirectEstimand g Pac Pbc ma mb mc - linkMarginal g Pt ma mb =
      (linkMarginal g Pac ma mc - linkMarginal g Pt ma mc) -
        (linkMarginal g Pbc mb mc - linkMarginal g Pt mb mc) := by
  simp only [marginalIndirectEstimand, linkMarginal]
  ring

/-- **No bias when the trials share the target's covariate law**, on every scale. -/
theorem marginalIndirectEstimand_self (g : ℝ → ℝ) (Pt : Measure 𝒳) (ma mb mc : 𝒳 → ℝ) :
    marginalIndirectEstimand g Pt Pt ma mb mc = linkMarginal g Pt ma mb := by
  simp only [marginalIndirectEstimand, linkMarginal]
  ring

/-- **The change of a marginal effect between two covariate laws through the averaging gaps.**
If the conditional effect of `c` against `t` is almost surely the constant `c₀` under two
probability laws `P` and `Q`, with integrable means and integrable link transforms, the change of
the marginal effect is `(J_P(m_c) - J_P(m_t)) - (J_Q(m_c) - J_Q(m_t))`. -/
theorem linkMarginal_sub_linkMarginal_eq_averagingGap {g : ℝ → ℝ} {P Q : Measure 𝒳}
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q] {mt mc : 𝒳 → ℝ} {c₀ : ℝ}
    (hP : ∀ᵐ x ∂P, linkContrast g mt mc x = c₀) (hQ : ∀ᵐ x ∂Q, linkContrast g mt mc x = c₀)
    (htP : Integrable mt P) (hcP : Integrable mc P) (htQ : Integrable mt Q)
    (hcQ : Integrable mc Q) (hgtP : Integrable (fun x => g (mt x)) P)
    (hgcP : Integrable (fun x => g (mc x)) P) (hgtQ : Integrable (fun x => g (mt x)) Q)
    (hgcQ : Integrable (fun x => g (mc x)) Q) :
    linkMarginal g P mt mc - linkMarginal g Q mt mc =
      (averagingGap g P mc - averagingGap g P mt) -
        (averagingGap g Q mc - averagingGap g Q mt) := by
  have e1 := linkMarginal_sub_linkConditional htP hcP hgtP hgcP
  have e2 := linkMarginal_sub_linkConditional htQ hcQ hgtQ hgcQ
  have c1 : linkConditional g P mt mc = c₀ := by
    rw [linkConditional, integral_congr_ae hP]; simp
  have c2 : linkConditional g Q mt mc = c₀ := by
    rw [linkConditional, integral_congr_ae hQ]; simp
  linarith

/-- **Without effect modification the bias of the marginal indirect comparison is a combination
of averaging gaps.** If the conditional effects of `c` against `a` and against `b` are almost
surely constant under the laws where they are used (both trials and the target), with
integrable means and link transforms, then the bias is
`[(J_ac(m_c) - J_ac(m_a)) - (J_*(m_c) - J_*(m_a))] - [(J_bc(m_c) - J_bc(m_b)) - (J_*(m_c) -
J_*(m_b))]`, with `J_ac`, `J_bc`, `J_*` the averaging gaps under `P_ac`, `P_bc`, `P_*`. -/
theorem marginalIndirectEstimand_sub_linkMarginal_eq_averagingGap {g : ℝ → ℝ}
    {Pac Pbc Pt : Measure 𝒳} [IsProbabilityMeasure Pac] [IsProbabilityMeasure Pbc]
    [IsProbabilityMeasure Pt] {ma mb mc : 𝒳 → ℝ} {c₁ c₂ : ℝ}
    (hac : ∀ᵐ x ∂Pac, linkContrast g ma mc x = c₁) (hact : ∀ᵐ x ∂Pt, linkContrast g ma mc x = c₁)
    (hbc : ∀ᵐ x ∂Pbc, linkContrast g mb mc x = c₂) (hbct : ∀ᵐ x ∂Pt, linkContrast g mb mc x = c₂)
    (hIac : Integrable ma Pac ∧ Integrable mc Pac ∧ Integrable (fun x => g (ma x)) Pac ∧
      Integrable (fun x => g (mc x)) Pac)
    (hIbc : Integrable mb Pbc ∧ Integrable mc Pbc ∧ Integrable (fun x => g (mb x)) Pbc ∧
      Integrable (fun x => g (mc x)) Pbc)
    (hIt : Integrable ma Pt ∧ Integrable mb Pt ∧ Integrable mc Pt ∧
      Integrable (fun x => g (ma x)) Pt ∧ Integrable (fun x => g (mb x)) Pt ∧
      Integrable (fun x => g (mc x)) Pt) :
    marginalIndirectEstimand g Pac Pbc ma mb mc - linkMarginal g Pt ma mb =
      ((averagingGap g Pac mc - averagingGap g Pac ma) -
          (averagingGap g Pt mc - averagingGap g Pt ma)) -
        ((averagingGap g Pbc mc - averagingGap g Pbc mb) -
          (averagingGap g Pt mc - averagingGap g Pt mb)) := by
  obtain ⟨a1, c1, a4, c4⟩ := hIac
  obtain ⟨b2, c2, b5, c5⟩ := hIbc
  obtain ⟨a3, b3, c3, a6, b6, c6⟩ := hIt
  rw [marginalIndirectEstimand_sub_linkMarginal,
    linkMarginal_sub_linkMarginal_eq_averagingGap hac hact a1 c1 a3 c3 a4 c4 a6 c6,
    linkMarginal_sub_linkMarginal_eq_averagingGap hbc hbct b2 c2 b3 c3 b5 c5 b6 c6]

end General

section Collapsible

variable {𝒳 : Type} [MeasurableSpace 𝒳]

/-- **On a collapsible scale the marginal indirect comparison is unbiased without effect
modification.** If the effect measure on the scale `g` with domain `D` is collapsible, the
conditional effects of `c` against `a` and against `b` are almost surely the constants `c₁`
and `c₂` under the laws where they are used, and the means are integrable with values in `D`,
then the indirect comparison of the marginal effects is the target marginal effect `c₁ - c₂`,
for all covariate laws of the trials and the target. -/
theorem marginalIndirectEstimand_eq_of_linkCollapsible {D : Set ℝ} {g : ℝ → ℝ}
    (hg : LinkCollapsible D g) {Pac Pbc Pt : Measure 𝒳} [IsProbabilityMeasure Pac]
    [IsProbabilityMeasure Pbc] [IsProbabilityMeasure Pt] {ma mb mc : 𝒳 → ℝ} {c₁ c₂ : ℝ}
    (hac : ∀ᵐ x ∂Pac, linkContrast g ma mc x = c₁) (hact : ∀ᵐ x ∂Pt, linkContrast g ma mc x = c₁)
    (hbc : ∀ᵐ x ∂Pbc, linkContrast g mb mc x = c₂) (hbct : ∀ᵐ x ∂Pt, linkContrast g mb mc x = c₂)
    (haI : Integrable ma Pac) (hcI : Integrable mc Pac) (hbI : Integrable mb Pbc)
    (hcI' : Integrable mc Pbc) (haT : Integrable ma Pt) (hbT : Integrable mb Pt)
    (hDac : ∀ᵐ x ∂Pac, ma x ∈ D ∧ mc x ∈ D) (hDbc : ∀ᵐ x ∂Pbc, mb x ∈ D ∧ mc x ∈ D)
    (hDt : ∀ᵐ x ∂Pt, ma x ∈ D ∧ mb x ∈ D) :
    marginalIndirectEstimand g Pac Pbc ma mb mc = c₁ - c₂ ∧
      linkMarginal g Pt ma mb = c₁ - c₂ := by
  have h1 := hg 𝒳 Pac ma mc haI hcI hDac c₁ hac
  have h2 := hg 𝒳 Pbc mb mc hbI hcI' hDbc c₂ hbc
  have hab : ∀ᵐ x ∂Pt, linkContrast g ma mb x = c₁ - c₂ := by
    filter_upwards [hact, hbct] with x h1 h2
    rw [linkContrast_eq_sub, h1, h2]
  exact ⟨by rw [marginalIndirectEstimand, h1, h2], hg 𝒳 Pt ma mb haT hbT hDt _ hab⟩

end Collapsible

/-! ### A model with bias and no effect modification -/

section LogitExample

/-- **Bias without effect modification on the logit scale.** Binary covariate `x`; comparator
risks `m_c = (1/5, 1/2)` at `x = false, true`, risks of `a` with conditional odds ratio `4`,
`m_a = (1/2, 4/5)`, and `m_b = m_c`. The conditional log odds ratio of `c` against `a` is
`log (1/4)` at both covariate values, that of `c` against `b` is `0`: no effect modification.
With the trial of `a` against `c` at `x = false`, the trial of `b` against `c` anywhere (here
also at `x = false`) and the target with two equally likely strata, the indirect comparison of
the marginal effects is `log (1/4)`, the target marginal effect is `log (49/169)`, and the bias is
`log (169/196) ≠ 0`. The marginal effect of `c` against `a` under the target law, `log (49/169)`,
differs from its value `log (1/4)` under the first trial's law. -/
theorem marginalIndirect_logit_bias_example :
    let mc : Bool → ℝ := fun x => if x then 1 / 2 else 1 / 5
    let ma : Bool → ℝ := fun x => if x then 4 / 5 else 1 / 2
    (∀ x, linkContrast logit ma mc x = Real.log (1 / 4)) ∧
      (∀ x, linkContrast logit mc mc x = 0) ∧
      marginalIndirectEstimand logit (Measure.dirac false) (Measure.dirac false) ma mc mc =
        Real.log (1 / 4) ∧
      linkMarginal logit halfLaw ma mc = Real.log (49 / 169) ∧
      marginalIndirectEstimand logit (Measure.dirac false) (Measure.dirac false) ma mc mc -
          linkMarginal logit halfLaw ma mc = Real.log (169 / 196) ∧
      Real.log (169 / 196) ≠ 0 := by
  intro mc ma
  have l15 : logit (1 / 5) = Real.log (1 / 4) := by norm_num [logit_eq_log_div]
  have l12 : logit (1 / 2) = 0 := by norm_num [logit_eq_log_div]
  have l45 : logit (4 / 5) = Real.log 4 := by norm_num [logit_eq_log_div]
  have l15' : logit 5⁻¹ = -Real.log 4 := by
    rw [← one_div, l15, one_div, Real.log_inv]
  have l12' : logit 2⁻¹ = 0 := by rw [← one_div, l12]
  have hhalf : ∀ f : Bool → ℝ, ∫ x, f x ∂halfLaw = (f true + f false) / 2 := integral_halfLaw
  have hm : linkMarginal logit halfLaw ma mc = Real.log (49 / 169) := by
    rw [linkMarginal, hhalf, hhalf]
    have e1 : (mc true + mc false) / 2 = 7 / 20 := by simp [mc]; norm_num
    have e2 : (ma true + ma false) / 2 = 13 / 20 := by simp [ma]; norm_num
    rw [e1, e2, logit_eq_log_div, logit_eq_log_div, ← Real.log_div (by norm_num) (by norm_num)]
    norm_num
  have hi : marginalIndirectEstimand logit (Measure.dirac false) (Measure.dirac false) ma mc mc =
      Real.log (1 / 4) := by
    simp only [marginalIndirectEstimand, linkMarginal, integral_dirac, sub_self, sub_zero]
    simp [ma, mc, l15', l12']
  refine ⟨fun x => ?_, fun x => sub_self _, hi, hm, ?_, ?_⟩
  · cases x
    · simp [linkContrast, ma, mc, l15', l12']
    · simp only [linkContrast, ma, mc, ite_true]
      rw [l12, l45, zero_sub, one_div, Real.log_inv]
  · rw [hi, hm, ← Real.log_div (by norm_num) (by norm_num)]
    norm_num
  · intro h
    rcases Real.log_eq_zero.1 h with h' | h' | h' <;> norm_num at h'

end LogitExample

/-! ### A binary covariate -/

section Bernoulli

/-- The **law of a binary covariate** with `P(x = true) = p`. -/
noncomputable def bernoulliLaw (p : ℝ) : Measure Bool :=
  stratumLaw fun v => if v then p else 1 - p

theorem isProbabilityMeasure_bernoulliLaw {p : ℝ} (h0 : 0 ≤ p) (h1 : p ≤ 1) :
    IsProbabilityMeasure (bernoulliLaw p) :=
  isProbabilityMeasure_stratumLaw ⟨fun v => by cases v <;> simp [h0, h1], by simp⟩

/-- Integrals against the binary law: `∫ f = (1 - p) f(false) + p f(true)`. -/
theorem integral_bernoulliLaw {p : ℝ} (h0 : 0 ≤ p) (h1 : p ≤ 1) (f : Bool → ℝ) :
    ∫ v, f v ∂bernoulliLaw p = (1 - p) * f false + p * f true := by
  rw [bernoulliLaw, integral_stratumLaw (fun v => by cases v <;> simp [h0, h1])]
  simp [standardizedRisk]
  ring

/-- **The marginal effect under a binary covariate**: the link applied to the mixtures
`(1 - p) m(false) + p m(true)`. -/
theorem linkMarginal_bernoulli (g : ℝ → ℝ) {p : ℝ} (h0 : 0 ≤ p) (h1 : p ≤ 1) (a b : Bool → ℝ) :
    linkMarginal g (bernoulliLaw p) a b =
      g ((1 - p) * b false + p * b true) - g ((1 - p) * a false + p * a true) := by
  rw [linkMarginal, integral_bernoulliLaw h0 h1, integral_bernoulliLaw h0 h1]

/-- **The exact bias of the marginal indirect comparison under a binary covariate**, with
`P(x = true)` equal to `p_ac`, `p_bc`, `p_*` in the two trials and the target, and the mixtures
`M_t(p) = (1 - p) m_t(false) + p m_t(true)`:
`[g(M_c(p_ac)) - g(M_a(p_ac))] - [g(M_c(p_bc)) - g(M_b(p_bc))] - [g(M_b(p_*)) - g(M_a(p_*))]`. -/
theorem marginalIndirectEstimand_bernoulli (g : ℝ → ℝ) {pac pbc ps : ℝ} (hac0 : 0 ≤ pac)
    (hac1 : pac ≤ 1) (hbc0 : 0 ≤ pbc) (hbc1 : pbc ≤ 1) (hs0 : 0 ≤ ps) (hs1 : ps ≤ 1)
    (ma mb mc : Bool → ℝ) :
    marginalIndirectEstimand g (bernoulliLaw pac) (bernoulliLaw pbc) ma mb mc -
        linkMarginal g (bernoulliLaw ps) ma mb =
      (g ((1 - pac) * mc false + pac * mc true) - g ((1 - pac) * ma false + pac * ma true)) -
        (g ((1 - pbc) * mc false + pbc * mc true) - g ((1 - pbc) * mb false + pbc * mb true)) -
        (g ((1 - ps) * mb false + ps * mb true) - g ((1 - ps) * ma false + ps * ma true)) := by
  rw [marginalIndirectEstimand, linkMarginal_bernoulli g hac0 hac1,
    linkMarginal_bernoulli g hbc0 hbc1, linkMarginal_bernoulli g hs0 hs1]

/-- **The bias of the anchored comparison of average conditional effects under a binary
covariate**: with `P(x = true)` equal to `p_ac`, `p_bc`, `p_*`, the anchored comparison minus the
target average conditional effect is `s_ac (p_ac - p_*) - s_bc (p_bc - p_*)`, where
`s_tc = τ_tc(true) - τ_tc(false)` is the effect modification of the contrast of `c` against `t`. -/
theorem anchoredConditional_bias_bernoulli (g : ℝ → ℝ) {pac pbc ps : ℝ} (hac0 : 0 ≤ pac)
    (hac1 : pac ≤ 1) (hbc0 : 0 ≤ pbc) (hbc1 : pbc ≤ 1) (hs0 : 0 ≤ ps) (hs1 : ps ≤ 1)
    (ma mb mc : Bool → ℝ) :
    (∫ x, linkContrast g ma mc x ∂bernoulliLaw pac -
          ∫ x, linkContrast g mb mc x ∂bernoulliLaw pbc) -
        linkConditional g (bernoulliLaw ps) ma mb =
      (linkContrast g ma mc true - linkContrast g ma mc false) * (pac - ps) -
        (linkContrast g mb mc true - linkContrast g mb mc false) * (pbc - ps) := by
  rw [linkConditional, integral_bernoulliLaw hac0 hac1, integral_bernoulliLaw hbc0 hbc1,
    integral_bernoulliLaw hs0 hs1]
  simp only [linkContrast]
  ring

/-- **The anchored conditional bias is genuine under effect modification**: if the contrast of
`c` against `a` is modified (`s_ac ≠ 0`) and the contrast of `c` against `b` is not, the bias is
nonzero as soon as `p_ac ≠ p_*`. -/
theorem anchoredConditional_bias_bernoulli_ne_zero (g : ℝ → ℝ) {pac pbc ps : ℝ}
    (hac0 : 0 ≤ pac) (hac1 : pac ≤ 1) (hbc0 : 0 ≤ pbc) (hbc1 : pbc ≤ 1) (hs0 : 0 ≤ ps)
    (hs1 : ps ≤ 1) {ma mb mc : Bool → ℝ}
    (hsac : linkContrast g ma mc true ≠ linkContrast g ma mc false)
    (hsbc : linkContrast g mb mc true = linkContrast g mb mc false) (hp : pac ≠ ps) :
    (∫ x, linkContrast g ma mc x ∂bernoulliLaw pac -
          ∫ x, linkContrast g mb mc x ∂bernoulliLaw pbc) -
        linkConditional g (bernoulliLaw ps) ma mb ≠ 0 := by
  rw [anchoredConditional_bias_bernoulli g hac0 hac1 hbc0 hbc1 hs0 hs1, hsbc, sub_self, zero_mul,
    sub_zero]
  exact mul_ne_zero (sub_ne_zero.2 hsac) (sub_ne_zero.2 hp)

end Bernoulli

/-! ### The anchored comparison of conditional effects on a general covariate space -/

section PointMasses

variable {𝒳 : Type*} [MeasurableSpace 𝒳] [MeasurableSingletonClass 𝒳]

/-- **A change of covariate law leaves an average contrast unchanged for all laws exactly
without effect modification**: `∫ τ dP = ∫ τ dQ` for all probability laws `P`, `Q` under which
`τ` is integrable iff `τ` is constant. -/
theorem integral_eq_forall_iff_const (τ : 𝒳 → ℝ) :
    (∀ (P Q : Measure 𝒳), IsProbabilityMeasure P → IsProbabilityMeasure Q → Integrable τ P →
      Integrable τ Q → ∫ x, τ x ∂P = ∫ x, τ x ∂Q) ↔ ∃ c, ∀ x, τ x = c := by
  constructor
  · intro h
    by_contra hne
    push Not at hne
    obtain ⟨x₀, -⟩ := hne 0
    obtain ⟨x₁, hx₁⟩ := hne (τ x₀)
    have := h (Measure.dirac x₁) (Measure.dirac x₀) inferInstance inferInstance
      (integrable_dirac (by simp)) (integrable_dirac (by simp))
    rw [integral_dirac, integral_dirac] at this
    exact hx₁ this
  · rintro ⟨c, hc⟩ P Q _ _ _ _
    simp [hc]

omit [MeasurableSingletonClass 𝒳] in
/-- **No effect modification, no anchored bias**: if both conditional contrasts against `c` are
constant, the anchored comparison of average conditional effects equals the target average
conditional effect for all probability laws of the trials and the target. -/
theorem anchoredConditional_bias_eq_zero_of_const (g : ℝ → ℝ) {ma mb mc : 𝒳 → ℝ} {c₁ c₂ : ℝ}
    (hac : ∀ x, linkContrast g ma mc x = c₁) (hbc : ∀ x, linkContrast g mb mc x = c₂)
    (Pac Pbc Pt : Measure 𝒳) [IsProbabilityMeasure Pac] [IsProbabilityMeasure Pbc]
    [IsProbabilityMeasure Pt] :
    (∫ x, linkContrast g ma mc x ∂Pac - ∫ x, linkContrast g mb mc x ∂Pbc) -
      linkConditional g Pt ma mb = 0 := by
  have hab : ∀ x, linkContrast g ma mb x = c₁ - c₂ := fun x => by
    rw [linkContrast_eq_sub, hac, hbc]
  simp [linkConditional, hac, hbc, hab]

/-- **Effect modification makes the anchored comparison biased for some covariate laws**: if the
contrast of `c` against `a` or of `c` against `b` is not constant, point mass laws of the trials
and the target give a nonzero bias. -/
theorem anchoredConditional_exists_bias_ne_zero (g : ℝ → ℝ) {ma mb mc : 𝒳 → ℝ}
    (h : (¬ ∃ c, ∀ x, linkContrast g ma mc x = c) ∨ ¬ ∃ c, ∀ x, linkContrast g mb mc x = c) :
    ∃ Pac Pbc Pt : Measure 𝒳, IsProbabilityMeasure Pac ∧ IsProbabilityMeasure Pbc ∧
      IsProbabilityMeasure Pt ∧
      (∫ x, linkContrast g ma mc x ∂Pac - ∫ x, linkContrast g mb mc x ∂Pbc) -
        linkConditional g Pt ma mb ≠ 0 := by
  have two : ∀ τ : 𝒳 → ℝ, (¬ ∃ c, ∀ x, τ x = c) → ∃ x₀ x₁, τ x₁ ≠ τ x₀ := fun τ hne => by
    push Not at hne
    obtain ⟨x₀, -⟩ := hne 0
    obtain ⟨x₁, hx₁⟩ := hne (τ x₀)
    exact ⟨x₀, x₁, hx₁⟩
  rcases h with h | h
  · obtain ⟨x₀, x₁, hx⟩ := two _ h
    refine ⟨Measure.dirac x₁, Measure.dirac x₀, Measure.dirac x₀, inferInstance, inferInstance,
      inferInstance, ?_⟩
    simp only [linkConditional, integral_dirac, linkContrast] at hx ⊢
    intro h0
    exact hx (by linarith)
  · obtain ⟨x₀, x₁, hx⟩ := two _ h
    refine ⟨Measure.dirac x₀, Measure.dirac x₁, Measure.dirac x₀, inferInstance, inferInstance,
      inferInstance, ?_⟩
    simp only [linkConditional, integral_dirac, linkContrast] at hx ⊢
    intro h0
    exact hx (by linarith)

/-- **An effect modifier breaks the constancy of the marginal effect**, on every scale: if the
conditional contrast takes two different values, two point mass covariate laws give different
marginal effects. -/
theorem exists_linkMarginal_ne {g : ℝ → ℝ} {a b : 𝒳 → ℝ} {x₁ x₂ : 𝒳}
    (h : linkContrast g a b x₁ ≠ linkContrast g a b x₂) :
    ∃ ν₁ ν₂ : Measure 𝒳, IsProbabilityMeasure ν₁ ∧ IsProbabilityMeasure ν₂ ∧
      linkMarginal g ν₁ a b ≠ linkMarginal g ν₂ a b := by
  refine ⟨Measure.dirac x₁, Measure.dirac x₂, inferInstance, inferInstance, ?_⟩
  simpa [linkMarginal, linkContrast] using h

end PointMasses

end NetworkMetaAnalysis

end CausalInference
