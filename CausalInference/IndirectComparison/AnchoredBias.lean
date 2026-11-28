/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.IndirectComparison.Basic
public import CausalInference.Measures.EffectModifier

/-!
# The bias of the anchored comparison, and prognostic variables

Let `m_a, m_b, m_c` be conditional mean functions of the three arms, common to the trial of `a`
against `c` (covariate law `P_ac`), the trial of `b` against `c` (covariate law `P_bc`) and the
target (covariate law `P_*`). The anchored comparison averages each trial's conditional effect
over its own covariate law, `∫ τ_ac dP_ac - ∫ τ_bc dP_bc`; the target average conditional effect
is `Δ_ab(P_*) = ∫ τ_ab dP_*`.

* **Bias decomposition** (`anchoredEstimand_sub_linkConditional`): the anchored comparison
  minus `Δ_ab(P_*)` is `b_ac - b_bc`, with `b_tc = ∫ τ_tc dP_tc - ∫ τ_tc dP_*`, the bias of each
  contrast from the difference between its trial's covariate law and the target's. With equal
  covariate laws there is no bias (`anchoredEstimand_eq_linkConditional_of_eq`); otherwise there
  can be (`anchored_bias_example`).
* **Prognostic variables cancel.** Split the covariate as `(x, w)`. If the conditional effects
  do not depend on `w`, each average conditional effect is an average over the law of `x` alone
  (`integral_linkContrast_eq_integral_fst`), so each bias term is computed from the laws of `x`
  (`anchoredBias_eq_map_fst`), and two settings with the same laws of `x` have the same anchored
  bias however imbalanced `w` is (`anchoredBias_eq_of_map_fst_eq`); `anchored_prognostic_example`
  verifies it in a model where `w` is prognostic and imbalanced.
* On any covariate space where `w` takes two values there are arms for which `w` is prognostic
  but not an effect modifier (`exists_prognostic_not_effectModifier`).

## Main results

* `anchoredEstimand_sub_linkConditional`, `anchoredEstimand_eq_linkConditional_of_eq`,
  `anchored_bias_example`.
* `integral_linkContrast_eq_integral_fst`, `anchoredBias_eq_map_fst`,
  `anchoredBias_eq_of_map_fst_eq`, `anchored_prognostic_example`,
  `exists_prognostic_not_effectModifier`.

## References

* D. M. Phillippo, A. E. Ades, S. Dias, S. Palmer, K. R. Abrams and N. J. Welton, *Methods for
  population-adjusted indirect comparisons in health technology appraisal*, Medical Decision
  Making 38 (2018).
-/

@[expose] public section

namespace CausalInference

namespace IndirectComparison

open MeasureTheory EffectMeasure

/-! ### The bias decomposition -/

section Decomposition

variable {𝒳 : Type*} [MeasurableSpace 𝒳] {g : ℝ → ℝ} {ma mb mc : 𝒳 → ℝ}

/-- **The bias decomposition of the anchored comparison.** For conditional effects integrable
under the target covariate law, the anchored comparison `∫ τ_ac dP_ac - ∫ τ_bc dP_bc` minus the
target average conditional effect `Δ_ab(P_*)` is `b_ac - b_bc`, where
`b_tc = ∫ τ_tc dP_tc - ∫ τ_tc dP_*`. The integrability of `τ_ac` under `P_ac` and of `τ_bc` under
`P_bc` makes each trial average a genuine integral. -/
theorem anchoredEstimand_sub_linkConditional {Pac Pbc Pt : Measure 𝒳}
    (_iac : Integrable (linkContrast g ma mc) Pac) (_ibc : Integrable (linkContrast g mb mc) Pbc)
    (iact : Integrable (linkContrast g ma mc) Pt) (ibct : Integrable (linkContrast g mb mc) Pt) :
    (∫ x, linkContrast g ma mc x ∂Pac - ∫ x, linkContrast g mb mc x ∂Pbc) -
        linkConditional g Pt ma mb =
      (∫ x, linkContrast g ma mc x ∂Pac - ∫ x, linkContrast g ma mc x ∂Pt) -
        (∫ x, linkContrast g mb mc x ∂Pbc - ∫ x, linkContrast g mb mc x ∂Pt) := by
  rw [linkConditional_eq_sub iact ibct, linkConditional, linkConditional]; ring

/-- **No bias when the trials share the target covariate law**: then the anchored estimand with
the target law is the target average conditional effect. -/
theorem anchoredEstimand_eq_linkConditional_of_eq {Pt : Measure 𝒳}
    (iact : Integrable (linkContrast g ma mc) Pt) (ibct : Integrable (linkContrast g mb mc) Pt) :
    anchoredEstimand Pt (linkContrast g ma mc) (linkContrast g mb mc) =
      linkConditional g Pt ma mb :=
  anchoredEstimand_linkContrast iact ibct

end Decomposition

/-- **An effect modifier imbalanced between a trial and the target biases the anchored
comparison.** On the identity scale with a binary covariate `x`, let `m_c = 0`, `m_a(x) = 0` and
`m_b(x) = 1{x}`, so `τ_ac = 0` and `τ_bc(x) = -1{x}`. With the trial laws concentrated at
`x = true` and the target at `x = false`, the anchored comparison is `1`, the target average
conditional effect is `0`, and the bias is `b_ac - b_bc = 0 - (-1) = 1`. -/
theorem anchored_bias_example :
    let mb : Bool → ℝ := fun x => if x then 1 else 0
    (∫ x, linkContrast id 0 0 x ∂Measure.dirac true -
        ∫ x, linkContrast id mb 0 x ∂Measure.dirac true) = 1 ∧
      linkConditional id (Measure.dirac false) 0 mb = 0 ∧
      (∫ x, linkContrast id 0 0 x ∂Measure.dirac true -
          ∫ x, linkContrast id mb 0 x ∂Measure.dirac true) -
        linkConditional id (Measure.dirac false) 0 mb = 1 := by
  intro mb
  simp [linkConditional, linkContrast, mb]

/-! ### Prognostic variables -/

section Prognostic

variable {𝒳 𝒲 : Type*} [MeasurableSpace 𝒳] [MeasurableSpace 𝒲] {g : ℝ → ℝ}
  {ma mb mc : 𝒳 × 𝒲 → ℝ}

/-- **An effect that does not depend on `w` averages over the law of `x` alone.** If the
conditional effect equals a measurable function `τ` of `x` at every `(x, w)`, its average over
any law `P` is `∫ τ d(P_x)`. -/
theorem integral_linkContrast_eq_integral_fst {τ : 𝒳 → ℝ}
    (h : ∀ x w, linkContrast g ma mb (x, w) = τ x) (hτ : Measurable τ) (P : Measure (𝒳 × 𝒲)) :
    ∫ p, linkContrast g ma mb p ∂P = ∫ x, τ x ∂(P.map Prod.fst) := by
  rw [integral_map measurable_fst.aemeasurable hτ.aestronglyMeasurable]
  exact integral_congr_ae (Filter.Eventually.of_forall fun p => h p.1 p.2)

/-- **Each bias term is computed from the laws of `x`.** If the conditional effects `τ_ac` and
`τ_bc` are measurable functions `τ₁`, `τ₂` of `x` alone, then each bias term `b_tc` is
`∫ τ d(P_tc,x) - ∫ τ d(P_*,x)`. -/
theorem anchoredBias_eq_map_fst {τ₁ τ₂ : 𝒳 → ℝ} (h₁ : ∀ x w, linkContrast g ma mc (x, w) = τ₁ x)
    (h₂ : ∀ x w, linkContrast g mb mc (x, w) = τ₂ x) (m₁ : Measurable τ₁) (m₂ : Measurable τ₂)
    (Pac Pbc Pt : Measure (𝒳 × 𝒲)) :
    (∫ p, linkContrast g ma mc p ∂Pac - ∫ p, linkContrast g ma mc p ∂Pt) =
        (∫ x, τ₁ x ∂(Pac.map Prod.fst) - ∫ x, τ₁ x ∂(Pt.map Prod.fst)) ∧
      (∫ p, linkContrast g mb mc p ∂Pbc - ∫ p, linkContrast g mb mc p ∂Pt) =
        (∫ x, τ₂ x ∂(Pbc.map Prod.fst) - ∫ x, τ₂ x ∂(Pt.map Prod.fst)) := by
  constructor <;>
    simp only [integral_linkContrast_eq_integral_fst h₁ m₁,
      integral_linkContrast_eq_integral_fst h₂ m₂]

/-- **The anchored bias does not see an imbalanced prognostic variable.** If the conditional
effects `τ_ac`, `τ_bc` are measurable functions of `x` alone, two settings
`(P_ac, P_bc, P_*)` and `(P'_ac, P'_bc, P'_*)` whose laws of `x` agree have the same anchored
bias `b_ac - b_bc`, whatever the laws of `w`. -/
theorem anchoredBias_eq_of_map_fst_eq {τ₁ τ₂ : 𝒳 → ℝ}
    (h₁ : ∀ x w, linkContrast g ma mc (x, w) = τ₁ x)
    (h₂ : ∀ x w, linkContrast g mb mc (x, w) = τ₂ x) (m₁ : Measurable τ₁) (m₂ : Measurable τ₂)
    {Pac Pbc Pt Pac' Pbc' Pt' : Measure (𝒳 × 𝒲)} (eac : Pac.map Prod.fst = Pac'.map Prod.fst)
    (ebc : Pbc.map Prod.fst = Pbc'.map Prod.fst) (et : Pt.map Prod.fst = Pt'.map Prod.fst) :
    (∫ p, linkContrast g ma mc p ∂Pac - ∫ p, linkContrast g ma mc p ∂Pt) -
        (∫ p, linkContrast g mb mc p ∂Pbc - ∫ p, linkContrast g mb mc p ∂Pt) =
      (∫ p, linkContrast g ma mc p ∂Pac' - ∫ p, linkContrast g ma mc p ∂Pt') -
        (∫ p, linkContrast g mb mc p ∂Pbc' - ∫ p, linkContrast g mb mc p ∂Pt') := by
  obtain ⟨e₁, e₂⟩ := anchoredBias_eq_map_fst (𝒲 := 𝒲) h₁ h₂ m₁ m₂ Pac Pbc Pt
  obtain ⟨e₁', e₂'⟩ := anchoredBias_eq_map_fst (𝒲 := 𝒲) h₁ h₂ m₁ m₂ Pac' Pbc' Pt'
  rw [e₁, e₂, e₁', e₂', eac, ebc, et]

end Prognostic

/-- **A prognostic, imbalanced, non-modifying variable causes no anchored bias.** On the identity
scale with covariates `(x, w) ∈ Bool × Bool`, let `m_c(x, w) = 1{w}`, `m_a = m_c` and
`m_b(x, w) = 1{w} + 1`: `w` is prognostic (it moves every arm) but not an effect modifier
(`τ_ac = 0`, `τ_bc = -1`). The trial of `a` against `c` is concentrated at `(true, true)`, the
trial of `b` against `c` at `(true, false)`, the target at `(true, true)`: `w` is imbalanced, yet
the anchored comparison `0 - (-1) = 1` is the target average conditional effect `1`. -/
theorem anchored_prognostic_example :
    let mc : Bool × Bool → ℝ := fun p => if p.2 then 1 else 0
    let mb : Bool × Bool → ℝ := fun p => (if p.2 then 1 else 0) + 1
    mc (true, true) ≠ mc (true, false) ∧ (∀ p, linkContrast id mc mc p = 0) ∧
      (∀ p, linkContrast id mb mc p = -1) ∧
      (∫ p, linkContrast id mc mc p ∂Measure.dirac (true, true) -
          ∫ p, linkContrast id mc mc p ∂Measure.dirac (true, true)) -
        (∫ p, linkContrast id mb mc p ∂Measure.dirac (true, false) -
          ∫ p, linkContrast id mb mc p ∂Measure.dirac (true, true)) = 0 ∧
      (∫ p, linkContrast id mc mc p ∂Measure.dirac (true, true) -
          ∫ p, linkContrast id mb mc p ∂Measure.dirac (true, false)) =
        linkConditional id (Measure.dirac (true, true)) mc mb ∧
      linkConditional id (Measure.dirac (true, true)) mc mb = 1 := by
  intro mc mb
  have h₁ : ∀ p, linkContrast id mc mc p = 0 := fun p => by simp [linkContrast]
  have h₂ : ∀ p, linkContrast id mb mc p = -1 := fun p => by simp [linkContrast, mb, mc]
  have hb := anchoredBias_eq_of_map_fst_eq (τ₁ := fun _ => (0 : ℝ)) (τ₂ := fun _ => (-1 : ℝ))
    (fun x w => h₁ (x, w)) (fun x w => h₂ (x, w)) measurable_const measurable_const
    (Pac := Measure.dirac (true, true)) (Pbc := Measure.dirac (true, false))
    (Pt := Measure.dirac (true, true)) (Pac' := Measure.dirac (true, true))
    (Pbc' := Measure.dirac (true, true)) (Pt' := Measure.dirac (true, true))
    (by simp) (by simp) rfl
  have hbias : (∫ p, linkContrast id mc mc p ∂Measure.dirac (true, true) -
          ∫ p, linkContrast id mc mc p ∂Measure.dirac (true, true)) -
        (∫ p, linkContrast id mb mc p ∂Measure.dirac (true, false) -
          ∫ p, linkContrast id mb mc p ∂Measure.dirac (true, true)) = 0 := by
    rw [hb]; ring
  have hdec := anchoredEstimand_sub_linkConditional (g := id) (ma := mc) (mb := mb) (mc := mc)
    (Pac := Measure.dirac (true, true)) (Pbc := Measure.dirac (true, false))
    (Pt := Measure.dirac (true, true)) Integrable.of_finite Integrable.of_finite
    Integrable.of_finite Integrable.of_finite
  have hc : linkConditional id (Measure.dirac (true, true)) mc mb = 1 := by
    simp [linkConditional, linkContrast, mb, mc]
  exact ⟨by simp [mc], h₁, h₂, hbias, by linarith, hc⟩

/-- **A prognostic variable need not be an effect modifier, on any covariate space**: whenever `w`
takes two values `w₁ ≠ w₂`, the arms `m_t(x, w) = m_c(x, w) = 1{w = w₁}` have conditional effect
`0` at every `(x, w)` on the identity scale, while `m_t(x, ·)` depends on `w`. -/
theorem exists_prognostic_not_effectModifier {𝒳 𝒲 : Type*} (x : 𝒳) {w₁ w₂ : 𝒲} (hw : w₁ ≠ w₂) :
    ∃ mt mc : 𝒳 × 𝒲 → ℝ, (∀ p, linkContrast id mc mt p = 0) ∧ mt (x, w₁) ≠ mt (x, w₂) := by
  classical
  exact ⟨fun p => if p.2 = w₁ then 1 else 0, fun p => if p.2 = w₁ then 1 else 0,
    fun _ => by simp [linkContrast], by simp [hw.symm]⟩

end IndirectComparison

end CausalInference
