/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.PopulationAdjustment.DensityRatio
public import CausalInference.PointTreatment.BalancingScore
public import CausalInference.PointTreatment.Randomized

/-!
# Population adjustment: the density ratio balances the covariates across the populations

Pool the trial (`S = true`) and the target (`S = false`) on one probability space with
covariates `X` and membership propensity `π(x) = P(S = true | X = x)`, with values in `(0, 1]`.
For `k > 0` the inverse odds `r(x) = k (1 - π(x)) / π(x)`, which for `k = P(S = 1) / P(S = 0)`
is the density ratio of the target covariate law with respect to the trial covariate law
(`map_restrict_eq_withDensity_armProb`), is a **balancing score for membership**: given `r(X)`,
membership `S` is conditionally independent of the covariates (`isBalancingScore_inverseOdds`).
The reason is that `π = k / (r + k)` is a function of `r`. Under logistic membership the
density ratio is the tilting weight `exp(log k - α̃ + (-β̃)ᵀx)`, which is therefore a balancing
score (`isBalancingScore_tiltWeight_logistic`). The pair `(S, X)` of two independent fair coins
is an instance (`isBalancingScore_inverseOdds_example`).

## Main results

* `isBalancingScore_inverseOdds` (the inverse odds `inverseOdds` and its basic lemmas are in
  `CausalInference.PopulationAdjustment.DensityRatio`).
* `tiltWeight_logistic_eq_inverseOdds`, `isBalancingScore_tiltWeight_logistic`.
* `isBalancingScore_inverseOdds_example`.

## References

* P. R. Rosenbaum and D. B. Rubin, *The central role of the propensity score in observational
  studies for causal effects*, Biometrika 70 (1983).
* D. Westreich, J. K. Edwards, C. R. Lesko, E. Stuart and S. R. Cole, *Transportability of
  trial results using inverse odds of sampling weights*, American Journal of Epidemiology 186
  (2017).
-/

@[expose] public section

namespace CausalInference

namespace PopulationAdjustment

open MeasureTheory ProbabilityTheory PointTreatment

variable {Ω 𝒳 : Type*} {mΩ : MeasurableSpace Ω} [MeasurableSpace 𝒳]

/-- **The inverse odds is a balancing score for membership**: if `π` is the propensity score of
membership `S` given `X`, nowhere zero, and `k ≠ 0`, then `S` is conditionally independent of
`X` given `k (1 - π(X)) / π(X)`. -/
theorem isBalancingScore_inverseOdds [StandardBorelSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
    {S : Ω → Bool} {X : Ω → 𝒳} {π : 𝒳 → ℝ} (hX : Measurable X) (hS : Measurable S)
    (hps : IsPropensityScore μ S X π) (hπ : ∀ x, π x ≠ 0) {k : ℝ} (hk : k ≠ 0) :
    IsBalancingScore μ S hX (measurable_inverseOdds hps.1 k) := by
  rw [hps.isBalancingScore_iff hX _ hS]
  exact ⟨fun y => k / (y + k), measurable_const.div (measurable_id.add measurable_const),
    Filter.Eventually.of_forall fun ω => (inverseOdds_comp_eq hπ hk (X ω)).symm⟩

variable {p : ℕ}

/-- Under logistic membership `π(x) = σ(α̃ + β̃ᵀx)` the tilting weight with intercept
`log k - α̃` and slope `-β̃` is the inverse odds, for `k > 0`. -/
theorem tiltWeight_logistic_eq_inverseOdds {k : ℝ} (hk : 0 < k) (α' : ℝ) (β' : Fin p → ℝ)
    (x : Fin p → ℝ) :
    tiltWeight id 0 (Real.log k - α') (-β') x =
      inverseOdds k (fun x => Real.sigmoid (α' + β' ⬝ᵥ x)) x := by
  rw [inverseOdds, one_sub_sigmoid_div_sigmoid, tiltWeight, Real.exp_add, Real.exp_sub,
    Real.exp_log hk]
  simp only [id, sub_zero, neg_dotProduct, neg_add]
  rw [Real.exp_add, Real.exp_neg α', div_eq_mul_inv]
  ring

/-- **The logistic tilting weight is a balancing score for membership**: under logistic
membership, `S` is conditionally independent of `X` given `exp(log k - α̃ + (-β̃)ᵀX)`, for every
`k > 0`. -/
theorem isBalancingScore_tiltWeight_logistic [StandardBorelSpace Ω] {μ : Measure Ω}
    [IsFiniteMeasure μ] {S : Ω → Bool} {X : Ω → Fin p → ℝ} {α' : ℝ} {β' : Fin p → ℝ}
    (hX : Measurable X) (hS : Measurable S)
    (hps : IsPropensityScore μ S X fun x => Real.sigmoid (α' + β' ⬝ᵥ x)) {k : ℝ} (hk : 0 < k) :
    IsBalancingScore μ S hX (measurable_tiltWeight id 0 (Real.log k - α') (-β') measurable_id) := by
  have h := isBalancingScore_inverseOdds hX hS hps (fun x => (Real.sigmoid_pos _).ne') hk.ne'
  have he : tiltWeight id 0 (Real.log k - α') (-β') =
      inverseOdds k (fun x => Real.sigmoid (α' + β' ⬝ᵥ x)) :=
    funext (tiltWeight_logistic_eq_inverseOdds hk α' β')
  unfold IsBalancingScore at h ⊢
  simp only [he]
  exact h

/-- **An instance**: for two independent fair coins `(S, X)` under `uniformPairLaw`, the
membership propensity is the constant `1/2` and the inverse odds with `k = 1` (the constant `1`)
is a balancing score for membership. -/
theorem isBalancingScore_inverseOdds_example :
    IsPropensityScore IndirectComparison.uniformPairLaw Prod.fst Prod.snd (fun _ => (1 : ℝ) / 2) ∧
      IsBalancingScore IndirectComparison.uniformPairLaw Prod.fst measurable_snd
        (measurable_inverseOdds (measurable_const (a := (1 : ℝ) / 2)) 1) := by
  have hind : IndepFun Prod.fst Prod.snd IndirectComparison.uniformPairLaw :=
    indepFun_prod (X := id) (Y := id) measurable_id measurable_id
  have hq : IndirectComparison.uniformPairLaw.real (Prod.fst ⁻¹' {true}) = 1 / 2 := by
    rw [← integral_indicator_one (measurable_fst (measurableSet_singleton true)),
      IndirectComparison.integral_uniformPairLaw]
    simp [Set.indicator]
    norm_num
  have hps := isPropensityScore_const_of_indepFun measurable_snd measurable_fst hind
  rw [hq] at hps
  exact ⟨hps, isBalancingScore_inverseOdds measurable_snd measurable_fst hps
    (fun _ => by norm_num) one_ne_zero⟩

end PopulationAdjustment

end CausalInference
