/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.NetworkMetaAnalysis.NetworkModel
public import CausalInference.Estimation.GaussianLinearImage

/-!
# Identification in arm based models and in network meta-regression

**Arm additive means.** A network of studies `j` with arm sets `arms j`, each containing its
baseline `base j`, and arm means `a_j + f_k` on the arms `(j, k)`.

* **What is identified** (`armAdditive_ident`, `armAdditive_ident_sub`): on a connected network
  the arm means determine the treatment effects `f_t - f_s` for all `s, t`, and with the
  normalization `f_r = 0` they determine `a` and `f`.
* **What is not.** Without a normalization `(a + c, f - c)` gives the same arm means for every
  `c` (`armAdditive_shift`); on a disconnected network the effect between two treatments in
  different components is not determined, even with `f_r = 0`
  (`armAdditive_not_ident_of_not_reachable`).

**Individual participant data network meta-regression.** On arm `(j, k)` the linear predictor at
covariate `x ∈ ℝ^ι` is `μ_j + xᵀ β₁ + d_k + xᵀ β_{2,k}` (`metaRegressionPredictor`), with
prognostic slope `β₁`, relative effects `d` and interactions `β₂`, normalized by `d_r = 0`,
`β_{2,r} = 0`. The covariate of study `j` has law `F_j`, common to its arms (randomization).

* **An affine function vanishing almost surely under a law with nonsingular covariance is zero**
  (`affine_eq_zero_of_ae`).
* **Identification** (`metaRegression_identifiable`): on a connected network with at least one
  study, if every `F_j` has second moments and a nonsingular covariance matrix (within study
  covariate variation in every direction), two parameter values with almost surely equal linear
  predictors on every arm coincide.
* **Failure without within study variation** (`metaRegression_not_identifiable_const`,
  `metaRegression_interaction_not_identifiable_const`): if the covariate is constant within each
  study (a point mass law `F_j = δ_{x_j}`), the prognostic slope is not identified; if moreover
  the constant is common to all studies, neither are the interactions.

## Main definitions

* `metaRegressionPredictor`.

## Main results

* `armAdditive_ident`, `armAdditive_ident_sub`, `armAdditive_shift`,
  `armAdditive_not_ident_of_not_reachable`.
* `affine_eq_zero_of_ae`, `metaRegression_identifiable`, `metaRegression_not_identifiable_const`,
  `metaRegression_interaction_not_identifiable_const`.

## References

* G. Lu and A. E. Ades, *Combination of direct and indirect evidence in mixed treatment
  comparisons*, Statistics in Medicine 23 (2004).
-/

@[expose] public section

namespace CausalInference

namespace NetworkMetaAnalysis

open Matrix MeasureTheory ProbabilityTheory BiasAnalysis.MeasurementError

variable {J K : Type*} [Finite J] [Finite K] {arms : J → Finset K} {base : J → K}

/-! ### Arm additive means -/

/-- **Arm additive means are identified on a connected network**: if `a_j + f_k = b_j + g_k` on
every arm, `f_r = g_r = 0` and the network is connected, then `a = b` and `f = g`. -/
theorem armAdditive_ident (hbase : ∀ j, base j ∈ arms j) (r : K)
    (hcon : (armContrastGraph arms base).Connected) {a b : J → ℝ} {f g : K → ℝ} (hf : f r = 0)
    (hg : g r = 0) (h : ∀ x : ArmIndex arms, a x.1.1 + f x.1.2 = b x.1.1 + g x.1.2) :
    a = b ∧ f = g := by
  have := Fintype.ofFinite J
  have := Fintype.ofFinite K
  classical
  have hinj := (armDesign_injective_iff hbase r).2 hcon
  have key : (Sum.elim (fun j => a j + f (base j)) (fun k => f k.1) : J ⊕ {k // k ≠ r} → ℝ) =
      Sum.elim (fun j => b j + g (base j)) (fun k => g k.1) := hinj (funext fun x => by
    rw [armDesign_mulVec, armDesign_mulVec]
    simp only [Sum.elim_inl, Sum.elim_comp_inr, padReference_restrict hf, padReference_restrict hg]
    have h1 := h x
    have h2 := h ⟨(x.1.1, base x.1.1), hbase _⟩
    simp only at h2
    linarith)
  have hfg : f = g := funext fun k => by
    by_cases hk : k = r
    · subst hk
      rw [hf, hg]
    · simpa using congrFun key (Sum.inr ⟨k, hk⟩)
  refine ⟨funext fun j => ?_, hfg⟩
  have := congrFun key (Sum.inl j)
  simp only [Sum.elim_inl, hfg] at this
  linarith

/-- **Without normalization the treatment effects are identified**: on a connected network,
equal arm means give equal effects `f_t - f_s` for all `s, t`, and intercepts that differ by the
constant `g_r - f_r`. -/
theorem armAdditive_ident_sub (hbase : ∀ j, base j ∈ arms j) (r : K)
    (hcon : (armContrastGraph arms base).Connected) {a b : J → ℝ} {f g : K → ℝ}
    (h : ∀ x : ArmIndex arms, a x.1.1 + f x.1.2 = b x.1.1 + g x.1.2) :
    (∀ s t, f t - f s = g t - g s) ∧ ∀ j, a j - b j = g r - f r := by
  obtain ⟨hab, hfg⟩ := armAdditive_ident (a := fun j => a j + f r) (b := fun j => b j + g r)
    (f := fun k => f k - f r) (g := fun k => g k - g r) hbase r hcon (sub_self _) (sub_self _)
    fun x => by have := h x; linarith
  refine ⟨fun s t => ?_, fun j => ?_⟩
  · have h1 := congrFun hfg t
    have h2 := congrFun hfg s
    linarith
  · have := congrFun hab j
    linarith

omit [Finite J] [Finite K] in
/-- **Without normalization the decomposition is not identified**: `(a + c, f - c)` gives the
same arm means as `(a, f)` for every `c`. -/
theorem armAdditive_shift (a : J → ℝ) (f : K → ℝ) (c : ℝ) (j : J) (k : K) :
    (a j + c) + (f k - c) = a j + f k := by
  ring

/-- **On a disconnected network the effect between components is not identified**: if `t` is not
reachable from `s`, then for every `(a, f)` with `f_r = 0` there are `(a', f')` with `f'_r = 0`
and the same arm means on every arm but a different effect `f'_t - f'_s`. -/
theorem armAdditive_not_ident_of_not_reachable (r : K) {s t : K}
    (hst : ¬(armContrastGraph arms base).Reachable s t) (a : J → ℝ) {f : K → ℝ} (hf : f r = 0) :
    ∃ (a' : J → ℝ) (f' : K → ℝ), f' r = 0 ∧
      (∀ x : ArmIndex arms, a' x.1.1 + f' x.1.2 = a x.1.1 + f x.1.2) ∧
      f' t - f' s ≠ f t - f s := by
  have := Fintype.ofFinite J
  have := Fintype.ofFinite K
  classical
  obtain ⟨d', hd', hne⟩ := armDesign_exists_ne_relativeEffect r hst
    (fun j => a j + f (base j)) (fun k => f k.1)
  refine ⟨fun j => a j + f (base j) - padReference r d' (base j), padReference r d',
    padReference_self r d', fun x => ?_, by rwa [padReference_restrict hf] at hne⟩
  have := congrFun hd' x
  rw [armDesign_mulVec, armDesign_mulVec] at this
  simp only [Sum.elim_inl, Sum.elim_comp_inr, padReference_restrict hf] at this
  linarith

/-! ### Network meta-regression -/

section MetaRegression

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The **linear predictor of the network meta-regression** on an arm of treatment `k` in a
study with intercept `μ`, at covariate `x`: `μ + xᵀ β₁ + d_k + xᵀ β_{2,k}`. -/
def metaRegressionPredictor (μ : ℝ) (β₁ : ι → ℝ) (d : K → ℝ) (β₂ : K → ι → ℝ) (k : K)
    (x : ι → ℝ) : ℝ :=
  μ + x ⬝ᵥ β₁ + d k + x ⬝ᵥ β₂ k

/-- **An affine function vanishing almost surely under a law with nonsingular covariance is
zero**: if `a + xᵀ b = 0` for `F`-almost every `x`, `F` has second moments and its covariance
matrix is nonsingular, then `a = 0` and `b = 0`. -/
theorem affine_eq_zero_of_ae {F : Measure (ι → ℝ)} [IsProbabilityMeasure F]
    (hF2 : ∀ i, MemLp (fun x : ι → ℝ => x i) 2 F)
    (hcov : (covMatrix F fun i x => x i).det ≠ 0) {a : ℝ} {b : ι → ℝ}
    (h : ∀ᵐ x ∂F, a + x ⬝ᵥ b = 0) : a = 0 ∧ b = 0 := by
  set S := covMatrix F fun i (x : ι → ℝ) => x i with hS
  have hvar : Var[fun x : ι → ℝ => ∑ i, b i * x i; F] = b ⬝ᵥ (S *ᵥ b) := by
    rw [BiasAnalysis.VarianceCovariance.variance_linearization_cov (fun i (x : ι → ℝ) => x i) hF2,
      BiasAnalysis.VarianceCovariance.quadraticVariance_eq_dotProduct]
  have hpsd : S.PosSemidef := posSemidef_covMatrix hF2
  have hae : (fun x : ι → ℝ => ∑ i, b i * x i) =ᵐ[F] fun _ => -a :=
    h.mono fun x hx => by
      have : x ⬝ᵥ b = ∑ i, b i * x i := by
        simp only [dotProduct]
        exact Finset.sum_congr rfl fun i _ => mul_comm _ _
      linarith
  have h0 : b ⬝ᵥ (S *ᵥ b) = 0 := by
    rw [← hvar, variance_congr hae, ← covariance_self aemeasurable_const, covariance_const_left]
  have hSb : S *ᵥ b = 0 := hpsd.dotProduct_mulVec_zero_iff.1 (by rw [star_trivial]; exact h0)
  have hb : b = 0 := eq_zero_of_mulVec_eq_zero hcov hSb
  refine ⟨?_, hb⟩
  obtain ⟨x, hx⟩ := h.exists
  rwa [hb, dotProduct_zero, add_zero] at hx

/-- **Identification of the network meta-regression.** On a connected network with at least one
study, if the covariate law `F_j` of every study has second moments and a nonsingular covariance
matrix, and two parameter values `(μ, β₁, d, β₂)`, `(μ', β₁', d', β₂')` with `d_r = d'_r = 0`,
`β_{2,r} = β'_{2,r} = 0` give almost surely equal linear predictors on every arm, then they are
equal. -/
theorem metaRegression_identifiable [Nonempty J] (hbase : ∀ j, base j ∈ arms j) (r : K)
    (hcon : (armContrastGraph arms base).Connected) (F : J → Measure (ι → ℝ))
    [∀ j, IsProbabilityMeasure (F j)] (hF2 : ∀ j i, MemLp (fun x : ι → ℝ => x i) 2 (F j))
    (hFcov : ∀ j, (covMatrix (F j) fun i x => x i).det ≠ 0) {μ μ' : J → ℝ} {β₁ β₁' : ι → ℝ}
    {d d' : K → ℝ} {β₂ β₂' : K → ι → ℝ} (hd : d r = 0) (hd' : d' r = 0) (hβ : β₂ r = 0)
    (hβ' : β₂' r = 0)
    (heq : ∀ x : ArmIndex arms, ∀ᵐ z ∂F x.1.1,
      metaRegressionPredictor (μ x.1.1) β₁ d β₂ x.1.2 z =
        metaRegressionPredictor (μ' x.1.1) β₁' d' β₂' x.1.2 z) :
    μ = μ' ∧ β₁ = β₁' ∧ d = d' ∧ β₂ = β₂' := by
  have hsplit : ∀ x : ArmIndex arms, μ x.1.1 + d x.1.2 = μ' x.1.1 + d' x.1.2 ∧
      β₁ + β₂ x.1.2 = β₁' + β₂' x.1.2 := by
    intro x
    have hF : ∀ᵐ z ∂F x.1.1, (μ x.1.1 + d x.1.2 - (μ' x.1.1 + d' x.1.2)) +
        z ⬝ᵥ ((β₁ + β₂ x.1.2) - (β₁' + β₂' x.1.2)) = 0 :=
      (heq x).mono fun z hz => by
        simp only [metaRegressionPredictor] at hz
        rw [dotProduct_sub, dotProduct_add, dotProduct_add]
        linarith
    obtain ⟨ha, hb⟩ := affine_eq_zero_of_ae (hF2 x.1.1) (hFcov x.1.1) hF
    exact ⟨by linarith, sub_eq_zero.1 hb⟩
  obtain ⟨hμ, hdeq⟩ := armAdditive_ident hbase r hcon hd hd' fun x => (hsplit x).1
  have hcoord : ∀ i, (fun _ : J => β₁ i) = (fun _ => β₁' i) ∧
      (fun k => β₂ k i) = fun k => β₂' k i := fun i =>
    armAdditive_ident (f := fun k => β₂ k i) (g := fun k => β₂' k i) hbase r hcon
      (by simp [hβ]) (by simp [hβ']) fun x => by
        simpa using congrFun (hsplit x).2 i
  refine ⟨hμ, funext fun i => ?_, hdeq, funext fun k => funext fun i => ?_⟩
  · exact congrFun (hcoord i).1 (Classical.arbitrary J)
  · exact congrFun (hcoord i).2 k

omit [Finite J] [Finite K] [DecidableEq ι] in
/-- **Without within study covariate variation the prognostic slope is not identified.** If the
covariate of study `j` is the constant `x_j` (law `δ_{x_j}`), then for every parameter value and
every `b ≠ 0` the slope `β₁ + b` with the intercepts `μ_j - x_jᵀ b` gives the same linear
predictor almost surely on every arm. -/
theorem metaRegression_not_identifiable_const (x₀ : J → ι → ℝ)
    (μ : J → ℝ) (β₁ : ι → ℝ) (d : K → ℝ) (β₂ : K → ι → ℝ) {b : ι → ℝ} (hb : b ≠ 0) :
    ∃ (μ' : J → ℝ) (β₁' : ι → ℝ), β₁' ≠ β₁ ∧ ∀ j k, ∀ᵐ z ∂Measure.dirac (x₀ j),
      metaRegressionPredictor (μ j) β₁ d β₂ k z = metaRegressionPredictor (μ' j) β₁' d β₂ k z := by
  refine ⟨fun j => μ j - x₀ j ⬝ᵥ b, β₁ + b, fun h => hb ?_, fun j k => ?_⟩
  · have := congrArg (· - β₁) h
    simpa using this
  · rw [ae_dirac_eq, Filter.eventually_pure]
    simp only [metaRegressionPredictor, dotProduct_add]
    ring

omit [Finite J] [Finite K] [DecidableEq ι] in
/-- **With a covariate constant across all studies the interactions are not identified.** If the
covariate is the same constant `x₀` in every study, then for every `b ≠ 0` and every treatment
`t ≠ r`, the interactions `β₂ + b 1{k = t}` with the effects `d - x₀ᵀ b 1{k = t}` keep the
normalization at `r` and give the same linear predictor almost surely on every arm. -/
theorem metaRegression_interaction_not_identifiable_const
    (x₀ : ι → ℝ) (μ : J → ℝ) (β₁ : ι → ℝ) (d : K → ℝ) (β₂ : K → ι → ℝ) {r t : K} (ht : t ≠ r)
    {b : ι → ℝ} (hb : b ≠ 0) :
    ∃ (d' : K → ℝ) (β₂' : K → ι → ℝ), d' r = d r ∧ β₂' r = β₂ r ∧ β₂' ≠ β₂ ∧
      ∀ j k, ∀ᵐ z ∂Measure.dirac x₀,
        metaRegressionPredictor (μ j) β₁ d β₂ k z =
          metaRegressionPredictor (μ j) β₁ d' β₂' k z := by
  classical
  refine ⟨fun k => d k - if k = t then x₀ ⬝ᵥ b else 0, fun k => β₂ k + if k = t then b else 0,
    by simp [Ne.symm ht], by simp [Ne.symm ht], fun h => hb ?_, fun j k => ?_⟩
  · have := congrFun h t
    simpa using this
  · rw [ae_dirac_eq, Filter.eventually_pure]
    by_cases hk : k = t
    · simp only [metaRegressionPredictor, hk, ite_true, dotProduct_add]
      ring
    · simp [metaRegressionPredictor, hk]

end MetaRegression

end NetworkMetaAnalysis

end CausalInference
