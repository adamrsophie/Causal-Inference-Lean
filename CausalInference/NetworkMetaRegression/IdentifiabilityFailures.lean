/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.NetworkMetaRegression.IdentifiabilityNetwork
public import CausalInference.NetworkMetaRegression.Examples

/-!
# Identifiability fails when one hypothesis is dropped

Each result below drops one hypothesis of `MultilevelModel.network_identifiable_of_class`,
`MultilevelModel.network_identifiable_of_shared` or `MultilevelModel.twoStudy_identifiable` and
gives two explicit parameter values with the same observable data (individual level surfaces and
aggregate arm means) and a different parameter or relative effect. The other hypotheses hold.

## Main definitions

* `disconnectedArms`, `disconnectedBase`: two studies, `a = 0` against `c = 2` and a single arm
  study of `b = 1`; the contrast graph does not join `b` with `c`.
* `triangleNetArms`, `triangleNetBase`: two studies, `a` against `c` and `b` against `c`; the
  contrast graph is connected (`triangleNet_connected`).
* `planeModel β`: the model with two covariates, prognostic effect `β` and all other parameters
  zero; `lineLaw`: the law with atoms `(0, 0)` and `(1, 1)` of mass `1/2` each, carried by the
  hyperplane `x₀ = x₁`.

## Main results

* `disconnected_failure`: in the disconnected network the models with `(μ₁, γ_b) = (0, 0)` and
  `(1, -1)` have the same surface on every arm, for every inverse link, so the same individual
  and aggregate data under all arm laws; the relative effects `γ_b - γ_a` are `0` and `-1`.
* `classModifiers_dropped_failure`: in the connected triangle network, with the identity link,
  binary arm laws with `P(X = 1) = 1/2` and individual data on both arms of study `0`, the models
  `(γ_b, β₂,b) = (0, 0)` and `(-1, 2)` give the same data; the second violates the class (shared)
  effect modifier assumption and its interaction `β₂,b` differs.
* `affineRank_dropped_failure`: with the covariate law `lineLaw` (no affine rank) the prognostic
  effects `(0, 0)` and `(1, -1)` give almost everywhere equal surfaces and equal aggregate means
  of every arm, for every inverse link.
* `anchoring_dropped_failure`: the models with `(μ, γ) = (0, 0)` and `(μ_j, γ_k) = (-1, 1)` give
  the same surface on every arm of every study; the second is not anchored at `c` and its
  `γ_a` differs.

## References

* D. M. Phillippo, S. Dias, A. E. Ades, M. Belger, A. Brnabic, A. Schacht, D. Saure, Z. Kadziola
  and N. J. Welton, *Multilevel network meta-regression for population-adjusted treatment
  comparisons*, Journal of the Royal Statistical Society Series A 183 (2020).
-/

@[expose] public section

namespace CausalInference

namespace NetworkMetaRegression

open MeasureTheory ProbabilityTheory NetworkMetaAnalysis MultilevelModel

/-- A triangle model with equal interactions of `a` and `b` shares the effect modifiers of all
non-reference treatments. -/
theorem triangleModel_shared_active (μ₀ μ₁ β γa γb δ : ℝ) :
    (triangleModel μ₀ μ₁ β γa γb δ δ).SharedEffectModifiers {k | k ≠ 2} := by
  intro s hs t ht
  fin_cases s <;> fin_cases t <;> simp_all [triangleModel, atBaseline]

/-! ### A disconnected network -/

/-- The arms of a disconnected network: study `0` compares `a = 0` with `c = 2`, study `1` has
the single arm `b = 1`. -/
def disconnectedArms : Fin 2 → Finset (Fin 3) := ![{0, 2}, {1}]

/-- The baselines of the disconnected network: `c` in study `0`, `b` in study `1`. -/
def disconnectedBase : Fin 2 → Fin 3 := ![2, 1]

theorem disconnectedBase_mem : ∀ j, disconnectedBase j ∈ disconnectedArms j := by decide

/-- The contrast graph of the disconnected network does not join `b` with `c`: no within study
contrast involves `b`. -/
theorem not_reachable_disconnected :
    ¬(armContrastGraph disconnectedArms disconnectedBase).Reachable 1 2 := by
  have hedge : ∀ e : ArmContrast disconnectedArms disconnectedBase,
      disconnectedBase e.1.1.1 ≠ 1 ∧ e.1.1.2 ≠ 1 := by decide
  have hno : ∀ x, ¬(armContrastGraph disconnectedArms disconnectedBase).Adj 1 x := by
    intro x h
    rw [armContrastGraph, comparisonGraph_adj] at h
    obtain ⟨-, ⟨e, h1, -⟩ | ⟨e, -, h2⟩⟩ := h
    · exact (hedge e).1 h1
    · exact (hedge e).2 h2
  have key : ∀ u v, (armContrastGraph disconnectedArms disconnectedBase).Walk u v → u = 1 →
      v = 1 := by
    intro u v w
    induction w with
    | nil => exact id
    | cons h _ _ =>
      rintro rfl
      exact absurd h (hno _)
  rintro ⟨w⟩
  exact absurd (key 1 2 w rfl) (by decide)

/-- **A disconnected network does not identify the relative effect.** The models
`triangleModel 0 0 0 0 0 0 0` and `triangleModel 0 1 0 0 (-1) 0 0` are anchored at `c` and share
their effect modifiers; on every arm of the disconnected network they have the same surface, for
every inverse link, so the same individual data and the same aggregate means under every arm law;
but the relative effects `γ_b - γ_a` are `0` and `-1`. -/
theorem disconnected_failure :
    let M := triangleModel 0 0 0 0 0 0 0
    let M' := triangleModel 0 1 0 0 (-1) 0 0
    ¬(armContrastGraph disconnectedArms disconnectedBase).Reachable 1 2 ∧
      M.IsAnchoredAt 2 ∧ M'.IsAnchoredAt 2 ∧ M.SharedEffectModifiers {k | k ≠ 2} ∧
      M'.SharedEffectModifiers {k | k ≠ 2} ∧
      (∀ (ginv : ℝ → ℝ) (x : ArmIndex disconnectedArms),
        M'.surface ginv (M'.μ x.1.1) x.1.2 = M.surface ginv (M.μ x.1.1) x.1.2) ∧
      M.γ 1 - M.γ 0 = 0 ∧ M'.γ 1 - M'.γ 0 = -1 := by
  intro M M'
  refine ⟨not_reachable_disconnected, triangleModel_anchored _ _ _ _ _ _ _,
    triangleModel_anchored _ _ _ _ _ _ _, triangleModel_shared_active _ _ _ _ _ _,
    triangleModel_shared_active _ _ _ _ _ _, ?_, by simp [M, triangleModel],
    by simp [M', triangleModel]⟩
  rintro ginv ⟨⟨j, k⟩, hk⟩
  funext y
  fin_cases j <;> fin_cases k <;> first
    | exact absurd hk (by decide)
    | simp [M, M', surface, eta_eq_affine, triangleModel]

/-! ### Dropping the class effect modifier assumption -/

/-- The arms of the triangle network: study `0` compares `a = 0` with `c = 2`, study `1`
compares `b = 1` with `c`. -/
def triangleNetArms : Fin 2 → Finset (Fin 3) := ![{0, 2}, {1, 2}]

/-- The baselines of the triangle network: `c` in both studies. -/
def triangleNetBase : Fin 2 → Fin 3 := ![2, 2]

theorem triangleNetBase_mem : ∀ j, triangleNetBase j ∈ triangleNetArms j := by decide

/-- The contrast graph of the triangle network is connected. -/
theorem triangleNet_connected : (armContrastGraph triangleNetArms triangleNetBase).Connected := by
  have h0 : (armContrastGraph triangleNetArms triangleNetBase).Adj 2 0 :=
    comparisonGraph_adj_of_ne (tail := fun e : ArmContrast triangleNetArms triangleNetBase =>
      triangleNetBase e.1.1.1) (head := fun e => e.1.1.2) ⟨⟨(0, 0), by decide⟩, by decide⟩
      (by decide)
  have h1 : (armContrastGraph triangleNetArms triangleNetBase).Adj 2 1 :=
    comparisonGraph_adj_of_ne (tail := fun e : ArmContrast triangleNetArms triangleNetBase =>
      triangleNetBase e.1.1.1) (head := fun e => e.1.1.2) ⟨⟨(1, 1), by decide⟩, by decide⟩
      (by decide)
  have hr : ∀ k, (armContrastGraph triangleNetArms triangleNetBase).Reachable 2 k := by
    intro k
    fin_cases k
    · exact h0.reachable
    · exact h1.reachable
    · exact SimpleGraph.Reachable.refl _
  exact ⟨fun u v => (hr u).symm.trans (hr v)⟩

/-- The arm `(0, 2)` of the reference in the individual data study of the triangle network. -/
def triangleNetRef : ArmIndex triangleNetArms := ⟨(0, 2), by decide⟩

/-- The arm `(0, 0)` of `a` in the individual data study of the triangle network. -/
def triangleNetA : ArmIndex triangleNetArms := ⟨(0, 0), by decide⟩

/-- **Without class effect modifiers the network is not identified.** In the connected triangle
network with the identity link and `binaryLaw (1/2)` on every arm (full affine rank), let
`M = triangleModel 0 0 0 0 0 0 0` and `M' = triangleModel 0 0 0 0 (-1) 0 2`. Both are anchored at
`c`; they have the same surfaces on the individual data arms `(0, 2)` and `(0, 0)` and the same
aggregate mean on every arm. `M` has class (here: shared) effect modifiers for the single class
of non-reference treatments, `M'` does not, and `β₂,b` differs. -/
theorem classModifiers_dropped_failure :
    let M := triangleModel 0 0 0 0 0 0 0
    let M' := triangleModel 0 0 0 0 (-1) 0 2
    (armContrastGraph triangleNetArms triangleNetBase).Connected ∧
      M.IsAnchoredAt 2 ∧ M'.IsAnchoredAt 2 ∧
      AffineRank (binaryLaw (1 / 2)) ∧
      (∀ α, M'.surface id α 2 = M.surface id α 2 ∧ M'.surface id α 0 = M.surface id α 0) ∧
      (∀ x : ArmIndex triangleNetArms,
        M'.armMean id (M'.μ x.1.1) (binaryLaw (1 / 2)) x.1.2 =
          M.armMean id (M.μ x.1.1) (binaryLaw (1 / 2)) x.1.2) ∧
      M.ClassEffectModifiers 2 (fun _ => ()) ∧ ¬M'.ClassEffectModifiers 2 (fun _ => ()) ∧
      M'.β₂ 1 ≠ M.β₂ 1 := by
  intro M M'
  have hI : (1 / 2 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := ⟨by norm_num, by norm_num⟩
  have hne : ∀ α t, t ≠ 1 → M'.surface id α t = M.surface id α t := fun α t ht =>
    surface_triangleModel_ne_b id 0 0 0 0 (-1) 0 0 2 0 α ht
  refine ⟨triangleNet_connected, triangleModel_anchored _ _ _ _ _ _ _,
    triangleModel_anchored _ _ _ _ _ _ _, affineRank_binaryLaw ⟨by norm_num, by norm_num⟩,
    fun α => ⟨hne α 2 (by decide), hne α 0 (by decide)⟩, ?_, ?_, ?_, ?_⟩
  · rintro ⟨⟨j, k⟩, hk⟩
    fin_cases j <;> fin_cases k
    · exact congrArg (fun f => ∫ y, f y ∂binaryLaw (1 / 2)) (hne _ 0 (by decide))
    · exact absurd hk (by decide)
    · exact congrArg (fun f => ∫ y, f y ∂binaryLaw (1 / 2)) (hne _ 2 (by decide))
    · exact absurd hk (by decide)
    · change (triangleModel 0 0 0 0 (-1) 0 2).armMean id _ (binaryLaw (1 / 2)) 1 =
        (triangleModel 0 0 0 0 0 0 0).armMean id _ (binaryLaw (1 / 2)) 1
      rw [armMean_triangleModel_b hI, armMean_triangleModel_b hI]
      norm_num [M, M', triangleModel]
    · exact congrArg (fun f => ∫ y, f y ∂binaryLaw (1 / 2)) (hne _ 2 (by decide))
  · intro _ s hs t ht
    exact (triangleModel_shared_active 0 0 0 0 0 0) s hs.1 t ht.1
  · intro h
    have := (classEffectModifiers_iff M' 2 _).1 h 0 1 (by decide) (by decide) rfl
    have := congrFun this 0
    norm_num [M', triangleModel] at this
  · intro h
    have := congrFun h 0
    norm_num [M, M', triangleModel] at this

/-! ### Dropping the affine rank condition -/

/-- The model with two covariates, prognostic effect `β` and all other parameters zero. -/
def planeModel (β : Fin 2 → ℝ) : MultilevelModel (Fin 2) (Fin 3) 2 where
  μ := fun _ => 0
  β₁ := β
  γ := fun _ => 0
  β₂ := fun _ _ => 0

/-- The law with atoms `(0, 0)` and `(1, 1)` of mass `1/2` each, on the hyperplane `x₀ = x₁`. -/
noncomputable abbrev lineLaw : Measure (Fin 2 → ℝ) := twoAtomLaw (fun _ => 0) (fun _ => 1) (1 / 2)

/-- **Without the affine rank condition the prognostic effect is not identified.** Under
`lineLaw`, a probability law whose two atoms lie on the hyperplane `x₀ = x₁` (so it fails
`AffineRank`, although each coordinate takes two values), the models `planeModel 0` and
`planeModel (1, -1)`, both anchored at `c` with shared effect modifiers, give almost everywhere
equal surfaces and equal aggregate means of every arm at every baseline, for every inverse link;
their prognostic effects differ. -/
theorem affineRank_dropped_failure :
    let M := planeModel 0
    let M' := planeModel ![1, -1]
    IsProbabilityMeasure lineLaw ∧ ¬AffineRank lineLaw ∧ M.IsAnchoredAt 2 ∧ M'.IsAnchoredAt 2 ∧
      M.SharedEffectModifiers {k | k ≠ 2} ∧ M'.SharedEffectModifiers {k | k ≠ 2} ∧
      (∀ (ginv : ℝ → ℝ) α t, M'.surface ginv α t =ᵐ[lineLaw] M.surface ginv α t) ∧
      (∀ (ginv : ℝ → ℝ) α t, M'.armMean ginv α lineLaw t = M.armMean ginv α lineLaw t) ∧
      M'.β₁ ≠ M.β₁ := by
  intro M M'
  have hS : ∀ᵐ x ∂lineLaw, x ∈ {x : Fin 2 → ℝ | x 0 = x 1} :=
    ae_twoAtomLaw (by simp) (by simp)
  have hae : ∀ (ginv : ℝ → ℝ) α t, M'.surface ginv α t =ᵐ[lineLaw] M.surface ginv α t := by
    intro ginv α t
    filter_upwards [hS] with x hx
    have hx : x 0 = x 1 := hx
    simp [M, M', surface, eta_eq_affine, planeModel, dotProduct, Fin.sum_univ_two, hx]
  refine ⟨isProbabilityMeasure_twoAtomLaw (by norm_num) (by norm_num), fun h => ?_, ⟨rfl, rfl⟩,
    ⟨rfl, rfl⟩, fun _ _ _ _ => rfl, fun _ _ _ _ => rfl, hae,
    fun ginv α t => integral_congr_ae (hae ginv α t), fun h => ?_⟩
  · have := (h 0 ![1, -1] (hS.mono fun x hx => by
      have hx : x 0 = x 1 := hx
      simp [dotProduct, Fin.sum_univ_two, hx])).2
    have := congrFun this 0
    norm_num at this
  · have := congrFun h 0
    norm_num [M, M', planeModel] at this

/-! ### Dropping the anchoring -/

/-- The model with one covariate, intercepts `-1`, effects `1` for every treatment and no
covariate effects: it is not anchored at `c`. -/
def shiftedModel : MultilevelModel (Fin 2) (Fin 3) 1 where
  μ := fun _ => -1
  β₁ := fun _ => 0
  γ := fun _ => 1
  β₂ := fun _ _ => 0

/-- **Without anchoring the effects are not identified.** The models
`triangleModel 0 0 0 0 0 0 0` and `shiftedModel` (intercepts `-1`, every effect `1`) share their
effect modifiers and have the same surface on every arm of every study, for every inverse link,
so the same individual data and the same aggregate means under all covariate laws; the second is
not anchored at `c`, and `γ_a` and the intercepts differ. -/
theorem anchoring_dropped_failure :
    let M := triangleModel 0 0 0 0 0 0 0
    M.IsAnchoredAt 2 ∧ ¬shiftedModel.IsAnchoredAt 2 ∧ M.SharedEffectModifiers {0, 1} ∧
      shiftedModel.SharedEffectModifiers {0, 1} ∧
      (∀ (ginv : ℝ → ℝ) (j : Fin 2) (t : Fin 3),
        shiftedModel.surface ginv (shiftedModel.μ j) t = M.surface ginv (M.μ j) t) ∧
      shiftedModel.γ 0 ≠ M.γ 0 ∧ shiftedModel.μ ≠ M.μ := by
  intro M
  refine ⟨triangleModel_anchored _ _ _ _ _ _ _, fun h => by
    have := h.1
    norm_num [shiftedModel] at this,
    (triangleModel_shared_iff _ _ _ _ _ _ _).2 rfl, fun _ _ _ _ => rfl, ?_, ?_, ?_⟩
  · intro ginv j t
    funext y
    fin_cases j <;> fin_cases t <;>
      simp [M, shiftedModel, surface, eta_eq_affine, triangleModel, dotProduct]
  · simp [M, shiftedModel, triangleModel]
  · intro h
    have := congrFun h 0
    norm_num [M, shiftedModel, triangleModel] at this

end NetworkMetaRegression

end CausalInference
