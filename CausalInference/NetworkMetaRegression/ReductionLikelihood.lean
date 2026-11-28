/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.NetworkMetaRegression.ReductionNetworkMetaAnalysis

/-!
# The likelihood of the multilevel model and its reductions

The multilevel network meta-regression likelihood (Phillippo et al. 2020) has two kinds of
factors. A record of individual data `(j, k, x, y)` (a patient of study `j` on treatment `k` with
covariates `x` and outcome `y`) contributes the individual outcome density `f(η_{jk}(x), y)` at
the linear predictor. A record of aggregate data `(j, k, y)` (a summary `y` of arm `k` of study
`j`) contributes the summary density `L(θ_{jk}, y)` at the aggregate arm mean
`θ_{jk} = ∫ g⁻¹(η_{jk}(x)) F_j(dx)`, the individual model integrated over the covariate law `F_j`
of the study.

* **The likelihood** (`MultilevelModel.likelihood`) and the **arm based network likelihood**
  (`armLikelihood`), in which an individual record contributes `f((X β)(j, k), y)` and an
  aggregate record `L(g⁻¹((X β)(j, k)), y)`, with `X` the arm design.
* **Without covariate effects the likelihood is the network likelihood**
  (`MultilevelModel.likelihood_eq_armLikelihood`): if `β₁ = 0` and `β₂ = 0`, then for every
  covariate law of the studies and every data set, the likelihood is the arm based network
  likelihood at `nmaCoef`, with the covariates of the individual records dropped. Conversely
  every arm based network likelihood is the likelihood of a model without covariate effects
  (`MultilevelModel.exists_likelihood_eq_armLikelihood`).
* **With individual data only** (`MultilevelModel.likelihood_nil`): with no aggregate records,
  the likelihood is the product of the individual factors at the network meta-regression
  predictor `α_j + xᵀβ₁ + γ_k + xᵀβ₂,k`, which does not involve the covariate laws, the inverse
  link of the aggregate factors or the summary density. This holds by unfolding the definition:
  the aggregate factor is an empty product.
* **On the identity link the aggregate factors are those of a meta-regression on the covariate
  means** (`MultilevelModel.likelihood_id`): if the covariates of each study have integrable
  coordinates, the aggregate arm mean is the predictor at the mean covariates,
  `θ_{jk} = η_{jk}(x̄_j)`, so no aggregation bias arises.

## Main definitions

* `MultilevelModel.likelihood`, `armLikelihood`, `MultilevelModel.ofArmCoef`.

## Main results

* `MultilevelModel.likelihood_eq_armLikelihood`,
  `MultilevelModel.exists_likelihood_eq_armLikelihood`, `MultilevelModel.likelihood_nil`,
  `MultilevelModel.likelihood_id`.

## References

* D. M. Phillippo, S. Dias, A. E. Ades, M. Belger, A. Brnabic, A. Schacht, D. Saure, Z. Kadziola
  and N. J. Welton, *Multilevel network meta-regression for population-adjusted treatment
  comparisons*, Journal of the Royal Statistical Society Series A 183 (2020).
-/

@[expose] public section

namespace CausalInference

namespace NetworkMetaRegression

open MeasureTheory ProbabilityTheory EffectMeasure IndirectComparison NetworkMetaAnalysis Matrix
open scoped ENNReal

variable {J K : Type*} {p : ℕ}

/-- The **arm based network likelihood** with individual density `f` (of the outcome given the
linear predictor), summary density `L` (of the summary given the arm mean) and inverse link `g⁻¹`:
an individual record `(a, y)` of the arm `a = (j, k)` contributes `f((X β) a, y)` and an aggregate
record `(a, y)` contributes `L(g⁻¹((X β) a), y)`, with `X` the arm design. -/
noncomputable def armLikelihood [Fintype J] [Fintype K] [DecidableEq J] [DecidableEq K]
    (f L : ℝ → ℝ → ℝ) (ginv : ℝ → ℝ) {arms : J → Finset K} (base : J → K) (r : K)
    (β : J ⊕ {k // k ≠ r} → ℝ) (ipd agd : List (ArmIndex arms × ℝ)) : ℝ≥0∞ :=
  (ipd.map fun d => ENNReal.ofReal (f ((armDesign arms base r *ᵥ β) d.1) d.2)).prod *
    (agd.map fun d => ENNReal.ofReal (L (ginv ((armDesign arms base r *ᵥ β) d.1)) d.2)).prod

namespace MultilevelModel

/-- The **likelihood of the multilevel model** with individual density `f` (of the outcome given
the linear predictor), summary density `L` (of the summary given the arm mean), inverse link
`g⁻¹` and covariate laws `F_j` of the studies: an individual record `(a, x, y)` of the arm
`a = (j, k)` contributes `f(η_{jk}(x), y)` and an aggregate record `(a, y)` contributes
`L(θ_{jk}, y)`, with `θ_{jk} = ∫ g⁻¹(η_{jk}) dF_j` the aggregate arm mean. -/
noncomputable def likelihood (f L : ℝ → ℝ → ℝ) (ginv : ℝ → ℝ) (M : MultilevelModel J K p)
    (F : J → Measure (Fin p → ℝ)) {arms : J → Finset K}
    (ipd : List (ArmIndex arms × (Fin p → ℝ) × ℝ)) (agd : List (ArmIndex arms × ℝ)) : ℝ≥0∞ :=
  (ipd.map fun d => ENNReal.ofReal (f (M.eta (M.μ d.1.1.1) d.1.1.2 d.2.1) d.2.2)).prod *
    (agd.map fun d =>
      ENNReal.ofReal (L (M.armMean ginv (M.μ d.1.1.1) (F d.1.1.1) d.1.1.2) d.2)).prod

/-- **With individual data only the likelihood is the individual data network meta-regression
likelihood**: with no aggregate records, the likelihood is the product of the individual factors
`f(μ_j + xᵀβ₁ + γ_k + xᵀβ₂,k, y)`, whatever the covariate laws, the summary density and the
inverse link. This holds by unfolding: the aggregate factor is the empty product `1`. -/
theorem likelihood_nil (f L : ℝ → ℝ → ℝ) (ginv : ℝ → ℝ) (M : MultilevelModel J K p)
    (F : J → Measure (Fin p → ℝ)) {arms : J → Finset K}
    (ipd : List (ArmIndex arms × (Fin p → ℝ) × ℝ)) :
    M.likelihood f L ginv F ipd [] = (ipd.map fun d => ENNReal.ofReal
      (f (metaRegressionPredictor (M.μ d.1.1.1) M.β₁ M.γ M.β₂ d.1.1.2 d.2.1) d.2.2)).prod := by
  simp [likelihood, eta]

variable [Fintype J] [Fintype K] [DecidableEq J] [DecidableEq K]

/-- **Without covariate effects the likelihood is the arm based network likelihood.** If
`β₁ = 0` and `β₂ = 0`, then for every family of covariate laws and every data set, the likelihood
of the multilevel model is the arm based network likelihood at `nmaCoef`, with the covariates of
the individual records dropped. -/
theorem likelihood_eq_armLikelihood (f L : ℝ → ℝ → ℝ) (ginv : ℝ → ℝ)
    (M : MultilevelModel J K p) (hβ₁ : M.β₁ = 0) (hβ₂ : ∀ k, M.β₂ k = 0)
    (F : J → Measure (Fin p → ℝ)) [∀ j, IsProbabilityMeasure (F j)] {arms : J → Finset K}
    (base : J → K) (r : K) (ipd : List (ArmIndex arms × (Fin p → ℝ) × ℝ))
    (agd : List (ArmIndex arms × ℝ)) :
    M.likelihood f L ginv F ipd agd =
      armLikelihood f L ginv base r (M.nmaCoef base r) (ipd.map fun d => (d.1, d.2.2)) agd := by
  simp only [likelihood, armLikelihood, List.map_map, Function.comp_def,
    eta_eq_armDesign_mulVec M hβ₁ hβ₂ base r, armMean_eq_armDesign_mulVec M hβ₁ hβ₂ F base r]

/-- The multilevel model without covariate effects, anchored at `r`, with the coefficients `β`
of the arm design: relative effects `d̃ = β ∘ inr` padded with `0` at `r`, and study baselines
`β_j - d̃_{b(j)}`. -/
def ofArmCoef (base : J → K) (r : K) (β : J ⊕ {k // k ≠ r} → ℝ) : MultilevelModel J K p :=
  ⟨fun j => β (Sum.inl j) - padReference r (β ∘ Sum.inr) (base j), 0,
    padReference r (β ∘ Sum.inr), fun _ => 0⟩

theorem armDesign_mulVec_nmaCoef_ofArmCoef {arms : J → Finset K} (base : J → K) (r : K)
    (β : J ⊕ {k // k ≠ r} → ℝ) :
    armDesign arms base r *ᵥ (ofArmCoef (p := p) base r β).nmaCoef base r =
      armDesign arms base r *ᵥ β := by
  funext a
  rw [armDesign_mulVec, armDesign_mulVec, padReference_nmaCoef, padReference_nmaCoef]
  simp only [nmaCoef, ofArmCoef, Sum.elim_inl, padReference_self]
  ring

/-- **Every arm based network likelihood is the likelihood of a model without covariate
effects**: for every coefficient vector `β` of the arm design, the model `ofArmCoef β` has
`β₁ = 0`, `β₂ = 0`, is anchored at `r`, and its likelihood is the arm based network likelihood at
`β` for every family of covariate laws and every data set. -/
theorem exists_likelihood_eq_armLikelihood (f L : ℝ → ℝ → ℝ) (ginv : ℝ → ℝ)
    {arms : J → Finset K} (base : J → K) (r : K) (β : J ⊕ {k // k ≠ r} → ℝ) :
    ∃ M : MultilevelModel J K p, M.β₁ = 0 ∧ (∀ k, M.β₂ k = 0) ∧ M.IsAnchoredAt r ∧
      ∀ (F : J → Measure (Fin p → ℝ)) [∀ j, IsProbabilityMeasure (F j)]
        (ipd : List (ArmIndex arms × (Fin p → ℝ) × ℝ)) (agd : List (ArmIndex arms × ℝ)),
        M.likelihood f L ginv F ipd agd =
          armLikelihood f L ginv base r β (ipd.map fun d => (d.1, d.2.2)) agd := by
  refine ⟨ofArmCoef base r β, rfl, fun _ => rfl, ⟨padReference_self r _, rfl⟩,
    fun F _ ipd agd => ?_⟩
  rw [likelihood_eq_armLikelihood f L ginv _ rfl (fun _ => rfl) F base r, armLikelihood,
    armLikelihood, armDesign_mulVec_nmaCoef_ofArmCoef]

omit [Fintype J] [Fintype K] [DecidableEq J] [DecidableEq K] in
/-- **On the identity link the likelihood is a meta-regression on the covariate means.** If the
covariates of each study have integrable coordinates, the aggregate factor of the arm `(j, k)` is
`L(η_{jk}(x̄_j), y)`, the summary density at the predictor evaluated at the mean covariates
`x̄_j` of the study. -/
theorem likelihood_id (f L : ℝ → ℝ → ℝ) (M : MultilevelModel J K p)
    (F : J → Measure (Fin p → ℝ)) [∀ j, IsProbabilityMeasure (F j)]
    (hF : ∀ j i, Integrable (fun x : Fin p → ℝ => x i) (F j)) {arms : J → Finset K}
    (ipd : List (ArmIndex arms × (Fin p → ℝ) × ℝ)) (agd : List (ArmIndex arms × ℝ)) :
    M.likelihood f L id F ipd agd =
      (ipd.map fun d => ENNReal.ofReal (f (M.eta (M.μ d.1.1.1) d.1.1.2 d.2.1) d.2.2)).prod *
        (agd.map fun d => ENNReal.ofReal
          (L (M.eta (M.μ d.1.1.1) d.1.1.2 (covMean (F d.1.1.1))) d.2)).prod := by
  have hmean : ∀ (α : ℝ) (j : J) (k : K), M.armMean id α (F j) k = M.eta α k (covMean (F j)) :=
    fun α j k => by
      have e : ∀ x, M.surface id α k x = (α + M.γ k) + ∑ i, x i * (M.β₁ + M.β₂ k) i :=
        fun x => by
          rw [surface, id, eta_eq_affine]
          rfl
      simp only [armMean, e]
      rw [integral_add (integrable_const _)
          (integrable_finsetSum _ fun i _ => (hF j i).mul_const _),
        integral_const, probReal_univ, one_smul,
        integral_finsetSum _ fun i _ => (hF j i).mul_const _, eta_eq_affine]
      simp only [integral_mul_const, covMean, dotProduct]
  simp only [likelihood, hmean]

end MultilevelModel

end NetworkMetaRegression

end CausalInference
