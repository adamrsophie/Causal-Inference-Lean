/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.PopulationAdjustment.WeightedConsistencyArm

/-!
# Consistency of the unanchored and anchored weighted comparisons

The arm means of the index trial are estimated by the weighted arm means with entropy balancing
weights at the reported target moments `t` (`sampleBalancedArmMean`); their consistency is
`sampleBalancedArmMean_isConsistent`. This file combines them into the comparisons with the
aggregate data trial. The index trial randomizes the arms `true` (the index treatment) and
`false` (the common comparator); in the target population `Q` these are the treatments `ta` and
`tc`, and `tb` is the treatment of the aggregate data trial.

* **Unanchored** (`unanchoredBalancedEstimate_isConsistent`): with a consistent estimate `m̂_B` of
  the target mean of `tb` and a link `g` continuous at the two target means,
  `g(m̂_B) - g(μ̂_true)` is consistent for `g(E_Q[Y(tb)]) - g(E_Q[Y(ta)])`. The index arm needs
  conditional constancy of its regression (it is a conditional mean function in `Q`).
* **Anchored on a link scale** (`anchoredBalancedEstimate_isConsistent`): the anchored weighted
  comparison `(g(μ̂_false) - g(μ̂_true)) - d̂_BC` (`anchoredWeightedEstimate` in the orientation
  `d̂_ac = g(μ̂_c) - g(μ̂_a)`) with `d̂_BC` consistent for `g(E_Q[Y(tc)]) - g(E_Q[Y(tb)])` and `g`
  continuous at the arm means is consistent for `g(E_Q[Y(tb)]) - g(E_Q[Y(ta)])`. Both arm
  regressions are conditional mean functions in `Q`.
* **Anchored on the identity scale** (`anchoredBalancedEstimate_isConsistent_identity`): only the
  conditional contrast `μ_false - μ_true` needs to be the conditional mean of `Y(tc) - Y(ta)` in
  `Q` (relative constancy on the identity scale); the arm regressions themselves may differ
  between the populations.

All side conditions (feasibility of the sample balancing problem, the size of the weights, the
measurability of the weights) are derived in `WeightedConsistencyArm` from the assumptions on the
law of the index trial records stated there.

## Main definitions

* `unanchoredBalancedEstimate`, `anchoredBalancedEstimate`.

## Main results

* `isConsistent_link_contrast`: the continuous mapping step.
* `unanchoredBalancedEstimate_isConsistent`, `anchoredBalancedEstimate_isConsistent`,
  `anchoredBalancedEstimate_isConsistent_identity`.

## References

* J. E. Signorovitch and coauthors, PharmacoEconomics 28 (2010).
* D. M. Phillippo, A. E. Ades, S. Dias, S. Palmer, K. R. Abrams and N. J. Welton, *Methods for
  population-adjusted indirect comparisons in health technology appraisal*, Medical Decision
  Making 38 (2018).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Finset
open scoped Topology

namespace CausalInference

namespace PopulationAdjustment

open PointTreatment IndirectComparison

variable {Ω 𝒳 : Type*} [MeasurableSpace Ω] [MeasurableSpace 𝒳] {p : ℕ}

/-! ### The estimators -/

/-- The **unanchored weighted comparison** `g(m̂_B) - g(μ̂_true)` of the index treatment with the
treatment of the aggregate data trial, from the estimate `m̂_B` of the target mean of the latter
and the weighted arm mean of the index treatment. -/
noncomputable def unanchoredBalancedEstimate (g : ℝ → ℝ) (φ : 𝒳 → Fin p → ℝ) (t : Fin p → ℝ)
    (O : ℕ → Ω → 𝒳 × Bool × ℝ) (mB : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  g (mB n ω) - g (sampleBalancedArmMean φ t O true n ω)

/-- The **anchored weighted comparison** `(g(μ̂_false) - g(μ̂_true)) - d̂_BC` with the entropy
balancing weights of the first `n` index trial records at the reported target moments `t`: the
library's `anchoredWeightedEstimate` with `ta = true` and `tc = false`. -/
noncomputable def anchoredBalancedEstimate (g : ℝ → ℝ) (φ : 𝒳 → Fin p → ℝ) (t : Fin p → ℝ)
    (O : ℕ → Ω → 𝒳 × Bool × ℝ) (dBC : ℕ → Ω → ℝ) (n : ℕ) : Ω → ℝ :=
  anchoredWeightedEstimate g (fun ω => balancingWeights fun i : Fin n => φ (O i ω).1 - t)
    (fun ω i => (O i ω).2.1) (fun ω i => (O i ω).2.2) true false (dBC n)

omit [MeasurableSpace Ω] [MeasurableSpace 𝒳] in
theorem anchoredBalancedEstimate_eq (g : ℝ → ℝ) (φ : 𝒳 → Fin p → ℝ) (t : Fin p → ℝ)
    (O : ℕ → Ω → 𝒳 × Bool × ℝ) (dBC : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) :
    anchoredBalancedEstimate g φ t O dBC n ω =
      g (sampleBalancedArmMean φ t O false n ω) - g (sampleBalancedArmMean φ t O true n ω) -
        dBC n ω := rfl

/-! ### The continuous mapping step -/

/-- **Contrasts of consistent estimates on a link scale.** If `â → α`, `ĉ → γ` and `d̂ → d` in
probability and `g` is continuous at `α` and `γ`, then `(g(ĉ) - g(â)) - d̂ → (g(γ) - g(α)) - d`. -/
theorem isConsistent_link_contrast {P : Measure Ω} {ahat chat dhat : ℕ → Ω → ℝ} {α γ d : ℝ}
    {g : ℝ → ℝ} (ha : IsConsistent ahat α P) (hc : IsConsistent chat γ P)
    (hd : IsConsistent dhat d P) (hga : ContinuousAt g α) (hgc : ContinuousAt g γ) :
    IsConsistent (fun n ω => g (chat n ω) - g (ahat n ω) - dhat n ω) (g γ - g α - d) P :=
  ((hc.comp_continuousAt hgc).sub (ha.comp_continuousAt hga)).sub hd

/-! ### Consistency -/

section Consistency

variable {P : Measure Ω} [IsProbabilityMeasure P] {O : ℕ → Ω → 𝒳 × Bool × ℝ}
  {Ω' ι : Type*} [MeasurableSpace Ω']

/-- **Consistency of the unanchored weighted comparison.** Assume the hypotheses of
`sampleBalancedArmMean_isConsistent` for the index arm `true` (i.i.d. records, randomized
assignment with `P(A = true) > 0`, the regression `E[Y | X, A] = μ_A(X)` with bounded conditional
residual variance, `μ_true = a₀ + bᵀφ` affine in the bounded measurable features, and the margin
condition at `t`), a target population `Q` with probability law, measurable covariates, feature
means `t` and integrable `Y(ta)` of which `μ_true` is a conditional mean function (conditional
constancy), a consistent estimate `m̂_B` of `E_Q[Y(tb)]`, and a link `g` continuous at the two
target means. Then `g(m̂_B) - g(μ̂_true) → g(E_Q[Y(tb)]) - g(E_Q[Y(ta)])` in probability. -/
theorem unanchoredBalancedEstimate_isConsistent (hO : IsIIDSample O P)
    (hOm : ∀ i, Measurable (O i)) {φ : 𝒳 → Fin p → ℝ} (hφ : Measurable φ) {t : Fin p → ℝ}
    {B : ℝ} (hB : ∀ x, ‖φ x - t‖ ≤ B) {δ : ℝ} (hδ : 0 < δ)
    (hmargin : ∀ v : Fin p → ℝ, ‖v‖ = 1 →
      δ ≤ (P.map (O 0)).real {z | δ ≤ v ⬝ᵥ (φ z.1 - t)})
    (hind : IndepFun (fun z : 𝒳 × Bool × ℝ => z.1) (fun z => z.2.1) (P.map (O 0)))
    (hq : 0 < (P.map (O 0)).real {z | z.2.1 = true})
    {mu : Bool → 𝒳 → ℝ} (hmu : ∀ s, Measurable (mu s))
    (hres2 : Integrable (fun z : 𝒳 × Bool × ℝ => (z.2.2 - mu z.2.1 z.1) ^ 2) (P.map (O 0)))
    (hreg : (P.map (O 0))[fun z => z.2.2 | MeasurableSpace.comap
      (fun z : 𝒳 × Bool × ℝ => (z.1, z.2.1)) inferInstance] =ᵐ[P.map (O 0)]
        fun z => mu z.2.1 z.1) {σ2 : ℝ}
    (hvar : (P.map (O 0))[fun z => (z.2.2 - mu z.2.1 z.1) ^ 2 |
      MeasurableSpace.comap (fun z : 𝒳 × Bool × ℝ => (z.1, z.2.1)) inferInstance]
        ≤ᵐ[P.map (O 0)] fun _ => σ2)
    {a0 : ℝ} {b : Fin p → ℝ} (haff : ∀ x, mu true x = a0 + b ⬝ᵥ φ x)
    {Q : Population Ω' 𝒳 ι} [IsProbabilityMeasure Q.μ] (hQX : Measurable Q.X)
    (ht : ∀ k, ∫ x, φ x k ∂Q.covLaw = t k) {ta tb : ι} (hQY : Integrable (Q.Y ta) Q.μ)
    (hQm : Q.IsCondMean ta (mu true)) {mB : ℕ → Ω → ℝ}
    (hmB : IsConsistent mB (Q.armMean tb) P) {g : ℝ → ℝ}
    (hga : ContinuousAt g (Q.armMean ta)) (hgb : ContinuousAt g (Q.armMean tb)) :
    IsConsistent (unanchoredBalancedEstimate g φ t O mB) (Q.marginalEffect g ta tb) P := by
  have hA := sampleBalancedArmMean_isConsistent hO hOm hφ hB hδ hmargin hind true hq hmu hres2
    hreg hvar haff
  rw [← integral_affine_covLaw hφ hB ht haff, hQm.integral_eq hQX hQY] at hA
  exact (hmB.comp_continuousAt hgb).sub (hA.comp_continuousAt hga)

/-- **Consistency of the anchored weighted comparison on a link scale.** Assume the hypotheses
of `sampleBalancedArmMean_isConsistent` for both arms of the index trial (with `P(A = true) > 0`
and `P(A = false) > 0`, and both arm regressions affine in the features, which makes them
measurable), a target population `Q`
as in `unanchoredBalancedEstimate_isConsistent` in which `μ_true` and `μ_false` are conditional
mean functions of the integrable outcomes `Y(ta)` and `Y(tc)`, an estimate `d̂_BC` of the aggregate
data trial consistent for `g(E_Q[Y(tc)]) - g(E_Q[Y(tb)])`, and a link `g` continuous at the
target means of `ta` and `tc`. Then the anchored comparison is consistent for
`g(E_Q[Y(tb)]) - g(E_Q[Y(ta)])`. -/
theorem anchoredBalancedEstimate_isConsistent (hO : IsIIDSample O P)
    (hOm : ∀ i, Measurable (O i)) {φ : 𝒳 → Fin p → ℝ} (hφ : Measurable φ) {t : Fin p → ℝ}
    {B : ℝ} (hB : ∀ x, ‖φ x - t‖ ≤ B) {δ : ℝ} (hδ : 0 < δ)
    (hmargin : ∀ v : Fin p → ℝ, ‖v‖ = 1 →
      δ ≤ (P.map (O 0)).real {z | δ ≤ v ⬝ᵥ (φ z.1 - t)})
    (hind : IndepFun (fun z : 𝒳 × Bool × ℝ => z.1) (fun z => z.2.1) (P.map (O 0)))
    (hqA : 0 < (P.map (O 0)).real {z | z.2.1 = true})
    (hqC : 0 < (P.map (O 0)).real {z | z.2.1 = false})
    {mu : Bool → 𝒳 → ℝ}
    (hres2 : Integrable (fun z : 𝒳 × Bool × ℝ => (z.2.2 - mu z.2.1 z.1) ^ 2) (P.map (O 0)))
    (hreg : (P.map (O 0))[fun z => z.2.2 | MeasurableSpace.comap
      (fun z : 𝒳 × Bool × ℝ => (z.1, z.2.1)) inferInstance] =ᵐ[P.map (O 0)]
        fun z => mu z.2.1 z.1) {σ2 : ℝ}
    (hvar : (P.map (O 0))[fun z => (z.2.2 - mu z.2.1 z.1) ^ 2 |
      MeasurableSpace.comap (fun z : 𝒳 × Bool × ℝ => (z.1, z.2.1)) inferInstance]
        ≤ᵐ[P.map (O 0)] fun _ => σ2)
    {a0A a0C : ℝ} {bA bC : Fin p → ℝ} (haffA : ∀ x, mu true x = a0A + bA ⬝ᵥ φ x)
    (haffC : ∀ x, mu false x = a0C + bC ⬝ᵥ φ x)
    {Q : Population Ω' 𝒳 ι} [IsProbabilityMeasure Q.μ] (hQX : Measurable Q.X)
    (ht : ∀ k, ∫ x, φ x k ∂Q.covLaw = t k) {ta tb tc : ι} (hQYa : Integrable (Q.Y ta) Q.μ)
    (hQYc : Integrable (Q.Y tc) Q.μ) (hQma : Q.IsCondMean ta (mu true))
    (hQmc : Q.IsCondMean tc (mu false)) {g : ℝ → ℝ} {dBC : ℕ → Ω → ℝ}
    (hBC : IsConsistent dBC (Q.marginalEffect g tb tc) P)
    (hga : ContinuousAt g (Q.armMean ta)) (hgc : ContinuousAt g (Q.armMean tc)) :
    IsConsistent (anchoredBalancedEstimate g φ t O dBC) (Q.marginalEffect g ta tb) P := by
  have hmu := measurable_regressions_of_affine hφ haffA haffC
  have hA := sampleBalancedArmMean_isConsistent hO hOm hφ hB hδ hmargin hind true hqA hmu hres2
    hreg hvar haffA
  rw [← integral_affine_covLaw hφ hB ht haffA, hQma.integral_eq hQX hQYa] at hA
  have hC := sampleBalancedArmMean_isConsistent hO hOm hφ hB hδ hmargin hind false hqC hmu hres2
    hreg hvar haffC
  rw [← integral_affine_covLaw hφ hB ht haffC, hQmc.integral_eq hQX hQYc] at hC
  have h := isConsistent_link_contrast hA hC hBC hga hgc
  have hlim : g (Q.armMean tc) - g (Q.armMean ta) - Q.marginalEffect g tb tc =
      Q.marginalEffect g ta tb := by
    simp only [Population.marginalEffect]; ring
  rw [hlim] at h
  exact h

/-- **Consistency of the anchored weighted comparison on the identity scale under relative
constancy.** Assume the hypotheses of `sampleBalancedArmMean_isConsistent` for both arms of the
index trial (both arm regressions affine in the features), a target population `Q` with
probability law, measurable covariates and feature means `t`, integrable `Y(ta)` and `Y(tc)`, and
only that the conditional contrast `μ_false - μ_true` of the index trial is the conditional mean
of `Y(tc) - Y(ta)` in `Q` (the arm regressions themselves need not carry over). If `d̂_BC` is
consistent for `E_Q[Y(tc)] - E_Q[Y(tb)]`, then `(μ̂_false - μ̂_true) - d̂_BC` is consistent for
`E_Q[Y(tb)] - E_Q[Y(ta)]`. -/
theorem anchoredBalancedEstimate_isConsistent_identity (hO : IsIIDSample O P)
    (hOm : ∀ i, Measurable (O i)) {φ : 𝒳 → Fin p → ℝ} (hφ : Measurable φ) {t : Fin p → ℝ}
    {B : ℝ} (hB : ∀ x, ‖φ x - t‖ ≤ B) {δ : ℝ} (hδ : 0 < δ)
    (hmargin : ∀ v : Fin p → ℝ, ‖v‖ = 1 →
      δ ≤ (P.map (O 0)).real {z | δ ≤ v ⬝ᵥ (φ z.1 - t)})
    (hind : IndepFun (fun z : 𝒳 × Bool × ℝ => z.1) (fun z => z.2.1) (P.map (O 0)))
    (hqA : 0 < (P.map (O 0)).real {z | z.2.1 = true})
    (hqC : 0 < (P.map (O 0)).real {z | z.2.1 = false})
    {mu : Bool → 𝒳 → ℝ}
    (hres2 : Integrable (fun z : 𝒳 × Bool × ℝ => (z.2.2 - mu z.2.1 z.1) ^ 2) (P.map (O 0)))
    (hreg : (P.map (O 0))[fun z => z.2.2 | MeasurableSpace.comap
      (fun z : 𝒳 × Bool × ℝ => (z.1, z.2.1)) inferInstance] =ᵐ[P.map (O 0)]
        fun z => mu z.2.1 z.1) {σ2 : ℝ}
    (hvar : (P.map (O 0))[fun z => (z.2.2 - mu z.2.1 z.1) ^ 2 |
      MeasurableSpace.comap (fun z : 𝒳 × Bool × ℝ => (z.1, z.2.1)) inferInstance]
        ≤ᵐ[P.map (O 0)] fun _ => σ2)
    {a0A a0C : ℝ} {bA bC : Fin p → ℝ} (haffA : ∀ x, mu true x = a0A + bA ⬝ᵥ φ x)
    (haffC : ∀ x, mu false x = a0C + bC ⬝ᵥ φ x)
    {Q : Population Ω' 𝒳 ι} [IsProbabilityMeasure Q.μ] (hQX : Measurable Q.X)
    (ht : ∀ k, ∫ x, φ x k ∂Q.covLaw = t k) {ta tb tc : ι} (hQYa : Integrable (Q.Y ta) Q.μ)
    (hQYc : Integrable (Q.Y tc) Q.μ)
    (hrel : (fun ω => mu false (Q.X ω) - mu true (Q.X ω)) =ᵐ[Q.μ]
      Q.μ[fun ω => Q.Y tc ω - Q.Y ta ω | MeasurableSpace.comap Q.X inferInstance])
    {dBC : ℕ → Ω → ℝ} (hBC : IsConsistent dBC (Q.marginalEffect id tb tc) P) :
    IsConsistent (anchoredBalancedEstimate id φ t O dBC) (Q.marginalEffect id ta tb) P := by
  have hmu := measurable_regressions_of_affine hφ haffA haffC
  have hA := sampleBalancedArmMean_isConsistent hO hOm hφ hB hδ hmargin hind true hqA hmu hres2
    hreg hvar haffA
  have hC := sampleBalancedArmMean_isConsistent hO hOm hφ hB hδ hmargin hind false hqC hmu hres2
    hreg hvar haffC
  have h := isConsistent_link_contrast hA hC hBC continuousAt_id continuousAt_id
  have haff : ∀ x, mu false x - mu true x = (a0C - a0A) + (bC - bA) ⬝ᵥ φ x := fun x => by
    rw [haffC, haffA, sub_dotProduct]; ring
  have hint := integral_affine_covLaw hφ hB ht haff
  have hid : ∫ ω, (Q.Y tc ω - Q.Y ta ω) ∂Q.μ = ∫ x, (mu false x - mu true x) ∂Q.covLaw :=
    Transport.integral_eq_integral_map_of_condExp (Y := fun ω => Q.Y tc ω - Q.Y ta ω)
      (f := fun x => mu false x - mu true x) hQX (hQYc.sub hQYa)
      ((hmu false).sub (hmu true)) hrel
  rw [integral_sub hQYc hQYa] at hid
  rw [hint] at hid
  have hlim : a0C + bC ⬝ᵥ t - (a0A + bA ⬝ᵥ t) - Q.marginalEffect id tb tc =
      Q.marginalEffect id ta tb := by
    simp only [Population.marginalEffect, Population.armMean, id] at hid ⊢
    rw [sub_dotProduct] at hid
    linarith
  simp only [id] at h hlim
  rw [hlim] at h
  exact h

end Consistency

end PopulationAdjustment

end CausalInference
