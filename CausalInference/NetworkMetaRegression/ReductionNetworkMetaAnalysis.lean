/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.NetworkMetaRegression.Estimands
public import CausalInference.NetworkMetaAnalysis.NetworkModel
public import CausalInference.NetworkMetaAnalysis.Consistency
public import CausalInference.IndirectComparison.CommonComparator

/-!
# Without covariate effects the multilevel model is the arm based network model

A multilevel network meta-regression model with no prognostic terms and no interactions
(`β₁ = 0`, `β₂ = 0`) has the arm mean `g⁻¹(μ_j + γ_k)` in study `j` and arm `k`, whatever the
covariate law of the study (`MultilevelModel.armMean_of_no_covariate_effects`). This file shows
that these models are exactly the arm based network meta-analysis model of
`NetworkMetaAnalysis.armDesign`, and that the relative effects they give satisfy the consistency
equations and the indirect comparison through a common comparator.

* **The coefficients of the network model** (`MultilevelModel.nmaCoef`): the study baseline
  `μ_j + γ_{b(j)}` on the baseline arm `b(j)` and the basic parameters `γ_k - γ_r` against the
  reference `r`.
* **The reduction** (`eta_eq_armDesign_mulVec`, `armMean_eq_armDesign_mulVec`,
  `link_armMean_eq_armDesign_mulVec`): without covariate effects, in every
  study and under every covariate law, the arm mean on the link scale is the arm design applied to
  `nmaCoef`.
* **Every arm based network model arises** (`exists_link_armMean_eq_armDesign_mulVec`): for every
  coefficient vector `β` of the arm design there is a multilevel model without covariate effects,
  anchored at `r`, whose link scale arm means are `X β`. So the two models have the same set of
  link scale arm means.
* **Consistency** (`isConsistent_linkMarginal_of_no_covariate_effects`): the marginal effects on
  the link scale form a consistent family, the same in every covariate law.
* **The indirect comparison** (`indirectEstimate_linkMarginal_of_no_covariate_effects`): for any
  three covariate laws, the indirect estimate `d_AC - d_BC` from the first two is the direct
  effect `d_AB` in the third, as in Bucher et al. (1997).

## Main definitions

* `MultilevelModel.nmaCoef`.

## Main results

* `MultilevelModel.eta_eq_armDesign_mulVec`, `MultilevelModel.armMean_eq_armDesign_mulVec`,
  `MultilevelModel.link_armMean_eq_armDesign_mulVec`,
  `MultilevelModel.exists_link_armMean_eq_armDesign_mulVec`,
  `MultilevelModel.isConsistent_linkMarginal_of_no_covariate_effects`,
  `MultilevelModel.indirectEstimate_linkMarginal_of_no_covariate_effects`.

## References

* H. C. Bucher, G. H. Guyatt, L. E. Griffith and S. D. Walter, *The results of direct and
  indirect treatment comparisons in meta-analysis of randomized controlled trials*, Journal of
  Clinical Epidemiology 50 (1997).
* D. M. Phillippo, S. Dias, A. E. Ades, M. Belger, A. Brnabic, A. Schacht, D. Saure, Z. Kadziola
  and N. J. Welton, *Multilevel network meta-regression for population-adjusted treatment
  comparisons*, Journal of the Royal Statistical Society Series A 183 (2020).
-/

@[expose] public section

namespace CausalInference

namespace NetworkMetaRegression

open MeasureTheory ProbabilityTheory EffectMeasure IndirectComparison NetworkMetaAnalysis Matrix

namespace MultilevelModel

variable {J K : Type*} {p : ℕ} {g ginv : ℝ → ℝ}

/-- The coefficients of the arm based network model given by a multilevel model: the study
baseline `μ_j + γ_{b(j)}` on the baseline arm `b(j)` of study `j`, and the basic parameter
`γ_k - γ_r` of each treatment `k ≠ r` against the reference `r`. -/
def nmaCoef (M : MultilevelModel J K p) (base : J → K) (r : K) : J ⊕ {k // k ≠ r} → ℝ :=
  Sum.elim (fun j => M.μ j + M.γ (base j)) fun k => M.γ k.1 - M.γ r

/-- The basic parameters of `nmaCoef`, padded with `0` at the reference, are `γ_t - γ_r`. -/
theorem padReference_nmaCoef [DecidableEq K] (M : MultilevelModel J K p) (base : J → K) (r t : K) :
    padReference r (M.nmaCoef base r ∘ Sum.inr) t = M.γ t - M.γ r := by
  by_cases h : t = r
  · subst h
    simp
  · rw [padReference_of_ne h]
    rfl

section Design

variable [Fintype J] [Fintype K] [DecidableEq J] [DecidableEq K]

/-- **Without covariate effects the predictor is the arm design.** If `β₁ = 0` and `β₂ = 0`, the
predictor of arm `(j, k)` at the study baseline `μ_j` is `(X β) (j, k)` with `β = nmaCoef`, at
every covariate value. -/
theorem eta_eq_armDesign_mulVec (M : MultilevelModel J K p) (hβ₁ : M.β₁ = 0)
    (hβ₂ : ∀ k, M.β₂ k = 0) {arms : J → Finset K} (base : J → K) (r : K) (a : ArmIndex arms)
    (x : Fin p → ℝ) :
    M.eta (M.μ a.1.1) a.1.2 x = (armDesign arms base r *ᵥ M.nmaCoef base r) a := by
  rw [(armMean_of_no_covariate_effects (g := id) (ginv := id) (fun _ => rfl) M hβ₁ hβ₂ _
    (Measure.dirac x)).1, armDesign_mulVec, padReference_nmaCoef, padReference_nmaCoef]
  simp only [nmaCoef, Sum.elim_inl]
  ring

/-- **Without covariate effects the arm mean is the inverse link of the arm design**: if
`β₁ = 0` and `β₂ = 0`, then for any covariate laws, `E_{F_j}[g⁻¹(η_{jk})] = g⁻¹((X β) (j, k))`
with `β = nmaCoef`. -/
theorem armMean_eq_armDesign_mulVec (M : MultilevelModel J K p) (hβ₁ : M.β₁ = 0)
    (hβ₂ : ∀ k, M.β₂ k = 0) (F : J → Measure (Fin p → ℝ)) [∀ j, IsProbabilityMeasure (F j)]
    {arms : J → Finset K} (base : J → K) (r : K) (a : ArmIndex arms) :
    M.armMean ginv (M.μ a.1.1) (F a.1.1) a.1.2 =
      ginv ((armDesign arms base r *ᵥ M.nmaCoef base r) a) := by
  simp only [armMean, surface, eta_eq_armDesign_mulVec M hβ₁ hβ₂ base r a, integral_const,
    probReal_univ, one_smul]

/-- **Without covariate effects the multilevel model is the arm based network model.** If
`g ∘ g⁻¹ = id`, `β₁ = 0` and `β₂ = 0`, then for any covariate laws `F_j` of the studies, the arm
mean of every arm `(j, k)` of the network, on the link scale, is the arm design applied to
`nmaCoef`: `g(E_{F_j}[g⁻¹(η_{jk})]) = μ_j + γ_k = (X β) (j, k)`. -/
theorem link_armMean_eq_armDesign_mulVec (hg : ∀ y, g (ginv y) = y)
    (M : MultilevelModel J K p) (hβ₁ : M.β₁ = 0) (hβ₂ : ∀ k, M.β₂ k = 0)
    (F : J → Measure (Fin p → ℝ)) [∀ j, IsProbabilityMeasure (F j)] {arms : J → Finset K}
    (base : J → K) (r : K) (a : ArmIndex arms) :
    g (M.armMean ginv (M.μ a.1.1) (F a.1.1) a.1.2) =
      (armDesign arms base r *ᵥ M.nmaCoef base r) a := by
  rw [armMean_eq_armDesign_mulVec M hβ₁ hβ₂ F base r a, hg]

/-- **Every arm based network model is a multilevel model without covariate effects.** For every
coefficient vector `β` of the arm design with reference `r` there is a multilevel model with
`β₁ = 0`, `β₂ = 0`, anchored at `r`, whose link scale arm means, under any covariate laws, are
`X β`. -/
theorem exists_link_armMean_eq_armDesign_mulVec (hg : ∀ y, g (ginv y) = y)
    {arms : J → Finset K} (base : J → K) (r : K) (β : J ⊕ {k // k ≠ r} → ℝ) :
    ∃ M : MultilevelModel J K p, M.β₁ = 0 ∧ (∀ k, M.β₂ k = 0) ∧ M.IsAnchoredAt r ∧
      ∀ (F : J → Measure (Fin p → ℝ)) [∀ j, IsProbabilityMeasure (F j)] (a : ArmIndex arms),
        g (M.armMean ginv (M.μ a.1.1) (F a.1.1) a.1.2) = (armDesign arms base r *ᵥ β) a := by
  set d := padReference r (β ∘ Sum.inr)
  refine ⟨⟨fun j => β (Sum.inl j) - d (base j), 0, d, fun _ => 0⟩, rfl, fun _ => rfl,
    ⟨padReference_self r _, rfl⟩, fun F _ a => ?_⟩
  rw [link_armMean_eq_armDesign_mulVec hg _ rfl (fun _ => rfl) F base r a, armDesign_mulVec,
    armDesign_mulVec, padReference_nmaCoef, padReference_nmaCoef]
  simp only [nmaCoef, Sum.elim_inl, padReference_self, d]
  ring

end Design

/-- **The relative effects without covariate effects are consistent.** If `g ∘ g⁻¹ = id`,
`β₁ = 0` and `β₂ = 0`, then in every covariate law `F` the marginal effects on the link scale,
`d_ab = g(E_F[g⁻¹ η_b]) - g(E_F[g⁻¹ η_a])`, form a consistent family, and they do not depend on
`F` or on the study baseline `α`. -/
theorem isConsistent_linkMarginal_of_no_covariate_effects (hg : ∀ y, g (ginv y) = y)
    (M : MultilevelModel J K p) (hβ₁ : M.β₁ = 0) (hβ₂ : ∀ k, M.β₂ k = 0) (α : ℝ)
    (F : Measure (Fin p → ℝ)) [IsProbabilityMeasure F] :
    NetworkMetaAnalysis.IsConsistent
        (fun a b : K => linkMarginal g F (M.surface ginv α a) (M.surface ginv α b)) ∧
      ∀ (α' : ℝ) (F' : Measure (Fin p → ℝ)) [IsProbabilityMeasure F'] (a b : K),
        linkMarginal g F (M.surface ginv α a) (M.surface ginv α b) =
          linkMarginal g F' (M.surface ginv α' a) (M.surface ginv α' b) := by
  have h := (armMean_of_no_covariate_effects hg M hβ₁ hβ₂ α F).2.2
  refine ⟨?_, fun α' F' _ a b => by
    rw [h, (armMean_of_no_covariate_effects hg M hβ₁ hβ₂ α' F').2.2]⟩
  simpa only [h] using isConsistent_sub M.γ

/-- **The indirect comparison through a common comparator.** If `g ∘ g⁻¹ = id`, `β₁ = 0` and
`β₂ = 0`, then for any three covariate laws `F_k`, `F_l`, `F_j` and baselines, the indirect
estimate `d_AC - d_BC`, with `d_AC` the marginal effect on the link scale in `F_k` and `d_BC` the
one in `F_l`, is the marginal effect `d_AB` in `F_j`. -/
theorem indirectEstimate_linkMarginal_of_no_covariate_effects (hg : ∀ y, g (ginv y) = y)
    (M : MultilevelModel J K p) (hβ₁ : M.β₁ = 0) (hβ₂ : ∀ k, M.β₂ k = 0) (αk αl αj : ℝ)
    (Fk Fl Fj : Measure (Fin p → ℝ)) [IsProbabilityMeasure Fk] [IsProbabilityMeasure Fl]
    [IsProbabilityMeasure Fj] (A B C : K) {Ω' : Type*} (ω : Ω') :
    indirectEstimate (fun _ => linkMarginal g Fk (M.surface ginv αk A) (M.surface ginv αk C))
        (fun _ => linkMarginal g Fl (M.surface ginv αl B) (M.surface ginv αl C)) ω =
      linkMarginal g Fj (M.surface ginv αj A) (M.surface ginv αj B) := by
  simp only [indirectEstimate, (armMean_of_no_covariate_effects hg M hβ₁ hβ₂ _ _).2.2]
  ring

end MultilevelModel

end NetworkMetaRegression

end CausalInference
