/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.NetworkMetaRegression.AggregateMonotone

/-!
# Identifiability in the two study network

The smallest network of multilevel network meta-regression: a study `jac` comparing `a` with the
reference `c` that reports **individual data**, and a study `jbc` comparing `b` with `c` that
reports **arm summaries** only. The data are:

* from `jac`: the conditional mean surfaces of arms `a` and `c`, almost everywhere under the arm
  covariate laws `F_a`, `F_c` (what the individual data identify when the outcome family is
  parameterized by its mean, `MultilevelModel.ae_surface_eq_of_compProd_eq`);
* from `jbc`: the aggregate means of arms `b` and `c` under the known covariate law `F_bc`.

## Main definitions

* `AffineRank F`: no nonzero affine function of the covariates vanishes `F`-almost everywhere
  (the full column rank of the individual design). It holds for a law with second moments and a
  nonsingular covariance matrix (`affineRank_of_covMatrix`).

## Main results

* `twoStudy_identifiable`: models anchored at `c` that share the effect modifiers of `a` and `b`,
  with a strictly increasing inverse link, individual data of full affine rank and integrable
  aggregate integrands, that reproduce these data have the same `μ_jac`, `μ_jbc`, `β₁`, `γ_a`,
  `γ_b`, `β₂,a`, `β₂,b`; hence the same surfaces of `a` and `b` at every baseline, so the same
  target estimands in every population (`twoStudy_surface_eq`).
* `twoStudy_steps`: without the shared effect modifier assumption the data still determine
  `μ_jac`, `β₁`, `γ_a`, `β₂,a` and `μ_jbc`; and the marginal effect of `b` against `a` in the
  population of the aggregate study, with its own baseline, is still identified
  (`twoStudy_comparator_identified`).
* Failure models: a constant inverse link (`twoStudy_not_identifiable_const_link`) and point mass
  covariate laws (`twoStudy_not_identifiable_dirac`). The failure without shared effect modifiers
  is in `SharedModifiersNecessary.lean`.

## References

* D. M. Phillippo, S. Dias, A. E. Ades, M. Belger, A. Brnabic, A. Schacht, D. Saure, Z. Kadziola
  and N. J. Welton, *Multilevel network meta-regression for population-adjusted treatment
  comparisons*, Journal of the Royal Statistical Society Series A 183 (2020).
-/

@[expose] public section

namespace CausalInference

namespace NetworkMetaRegression

open MeasureTheory ProbabilityTheory EffectMeasure NetworkMetaAnalysis

variable {p : ℕ}

/-- The **affine rank condition** on a covariate law `F`: an affine function `s + xᵀb` that
vanishes `F`-almost everywhere is zero. -/
def AffineRank (F : Measure (Fin p → ℝ)) : Prop :=
  ∀ (s : ℝ) (b : Fin p → ℝ), (∀ᵐ x ∂F, s + x ⬝ᵥ b = 0) → s = 0 ∧ b = 0

/-- A probability law with second moments and a nonsingular covariance matrix has full affine
rank. -/
theorem affineRank_of_covMatrix {F : Measure (Fin p → ℝ)} [IsProbabilityMeasure F]
    (hF2 : ∀ i, MemLp (fun x : Fin p → ℝ => x i) 2 F)
    (hcov : (BiasAnalysis.MeasurementError.covMatrix F fun i x => x i).det ≠ 0) :
    AffineRank F :=
  fun _ _ h => affine_eq_zero_of_ae hF2 hcov h

/-- Two affine functions that agree almost everywhere under a law of full affine rank have the
same intercept and slope. -/
theorem AffineRank.eq {F : Measure (Fin p → ℝ)} (hF : AffineRank F) {s s' : ℝ}
    {b b' : Fin p → ℝ} (h : ∀ᵐ x ∂F, s + x ⬝ᵥ b = s' + x ⬝ᵥ b') : s = s' ∧ b = b' := by
  have := hF (s - s') (b - b') (h.mono fun x hx => by rw [dotProduct_sub]; linarith)
  exact ⟨sub_eq_zero.1 this.1, sub_eq_zero.1 this.2⟩

namespace MultilevelModel

variable {J K : Type*}

/-- Almost everywhere equal surfaces of one arm under a law of full affine rank, for a strictly
increasing inverse link, give equal cell intercepts and equal slope vectors. -/
theorem cell_eq_of_ae_surface_eq {ginv : ℝ → ℝ} (hmono : StrictMono ginv)
    {F : Measure (Fin p → ℝ)} (hF : AffineRank F) {M M' : MultilevelModel J K p} {α α' : ℝ}
    {k : K} (h : M.surface ginv α k =ᵐ[F] M'.surface ginv α' k) :
    α + M.γ k = α' + M'.γ k ∧ M.β₁ + M.β₂ k = M'.β₁ + M'.β₂ k :=
  hF.eq (h.mono fun x hx => by
    rw [← eta_eq_affine, ← eta_eq_affine]
    exact hmono.injective hx)

variable {ginv : ℝ → ℝ} {Fa Fc Fbc : Measure (Fin p → ℝ)} {M M' : MultilevelModel J K p}
  {jac jbc : J} {a b c : K}

/-- **The steps that need no shared effect modifiers.** Models anchored at `c`, a strictly
increasing inverse link, individual data of `jac` with full affine rank, and an integrable
aggregate integrand of arm `c` of `jbc` for the first model: equal surfaces of `a` and `c` in
`jac` and an equal aggregate mean of `c` in `jbc` give equal `μ_jac`, `β₁`, `γ_a`, `β₂,a` and
`μ_jbc`. -/
theorem twoStudy_steps (hmono : StrictMono ginv) [IsProbabilityMeasure Fbc] (hra : AffineRank Fa)
    (hrc : AffineRank Fc) (hM : M.IsAnchoredAt c) (hM' : M'.IsAnchoredAt c)
    (hintc : ∀ s, Integrable (fun x => ginv (s + x ⬝ᵥ (M.β₁ + M.β₂ c))) Fbc)
    (ipda : M.surface ginv (M.μ jac) a =ᵐ[Fa] M'.surface ginv (M'.μ jac) a)
    (ipdc : M.surface ginv (M.μ jac) c =ᵐ[Fc] M'.surface ginv (M'.μ jac) c)
    (agdc : M.armMean ginv (M.μ jbc) Fbc c = M'.armMean ginv (M'.μ jbc) Fbc c) :
    M.μ jac = M'.μ jac ∧ M.β₁ = M'.β₁ ∧ M.γ a = M'.γ a ∧ M.β₂ a = M'.β₂ a ∧
      M.μ jbc = M'.μ jbc := by
  obtain ⟨hγc, hβc⟩ := hM
  obtain ⟨hγc', hβc'⟩ := hM'
  obtain ⟨h1, h2⟩ := cell_eq_of_ae_surface_eq hmono hrc ipdc
  rw [hγc, hγc', add_zero, add_zero] at h1
  rw [hβc, hβc', add_zero, add_zero] at h2
  obtain ⟨h3, h4⟩ := cell_eq_of_ae_surface_eq hmono hra ipda
  rw [h2] at h4
  have h5 := intercept_eq_of_armMean_eq hmono (by rw [hβc, hβc', h2]) hintc agdc
  rw [hγc, hγc', add_zero, add_zero] at h5
  exact ⟨h1, h2, by linarith, add_left_cancel h4, h5⟩

/-- **Identifiability in the two study network under shared effect modifiers.** Let `M`, `M'` be
anchored at `c` and share the effect modifiers of `a` and `b`; let `g⁻¹` be strictly increasing,
the arm covariate laws `F_a`, `F_c` of the individual data study `jac` have full affine rank,
`F_bc` be a probability law, and `g⁻¹(s + xᵀ(β₁ + β₂,t))` be integrable under `F_bc` for every
`s` and `t = b, c` (for `M`). If the two models give almost everywhere equal surfaces of `a` and
`c` in `jac` and equal aggregate means of `b` and `c` in `jbc`, they have the same `μ_jac`,
`μ_jbc`, `β₁`, `γ_a`, `γ_b`, `β₂,a` and `β₂,b`. -/
theorem twoStudy_identifiable (hmono : StrictMono ginv) [IsProbabilityMeasure Fbc]
    (hra : AffineRank Fa) (hrc : AffineRank Fc) (hM : M.IsAnchoredAt c)
    (hM' : M'.IsAnchoredAt c) (hS : M.SharedEffectModifiers {a, b})
    (hS' : M'.SharedEffectModifiers {a, b})
    (hintb : ∀ s, Integrable (fun x => ginv (s + x ⬝ᵥ (M.β₁ + M.β₂ b))) Fbc)
    (hintc : ∀ s, Integrable (fun x => ginv (s + x ⬝ᵥ (M.β₁ + M.β₂ c))) Fbc)
    (ipda : M.surface ginv (M.μ jac) a =ᵐ[Fa] M'.surface ginv (M'.μ jac) a)
    (ipdc : M.surface ginv (M.μ jac) c =ᵐ[Fc] M'.surface ginv (M'.μ jac) c)
    (agdb : M.armMean ginv (M.μ jbc) Fbc b = M'.armMean ginv (M'.μ jbc) Fbc b)
    (agdc : M.armMean ginv (M.μ jbc) Fbc c = M'.armMean ginv (M'.μ jbc) Fbc c) :
    M.μ jac = M'.μ jac ∧ M.μ jbc = M'.μ jbc ∧ M.β₁ = M'.β₁ ∧ M.γ a = M'.γ a ∧
      M.γ b = M'.γ b ∧ M.β₂ a = M'.β₂ a ∧ M.β₂ b = M'.β₂ b := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := twoStudy_steps hmono hra hrc hM hM' hintc ipda ipdc agdc
  have hb : M.β₂ b = M.β₂ a := hS b (by simp) a (by simp)
  have hb' : M'.β₂ b = M'.β₂ a := hS' b (by simp) a (by simp)
  have h6 := intercept_eq_of_armMean_eq hmono (by rw [hb, hb', h2, h4]) hintb agdb
  rw [h5] at h6
  exact ⟨h1, h5, h2, h3, add_left_cancel h6, h4, by rw [hb, hb', h4]⟩

/-- **The target estimands are identified**: under the hypotheses of `twoStudy_identifiable` the
two models have the same surfaces of `a` and `b` at every baseline, so the same marginal and
conditional estimands of `b` against `a` in every target population. -/
theorem twoStudy_surface_eq (hmono : StrictMono ginv) [IsProbabilityMeasure Fbc]
    (hra : AffineRank Fa) (hrc : AffineRank Fc) (hM : M.IsAnchoredAt c)
    (hM' : M'.IsAnchoredAt c) (hS : M.SharedEffectModifiers {a, b})
    (hS' : M'.SharedEffectModifiers {a, b})
    (hintb : ∀ s, Integrable (fun x => ginv (s + x ⬝ᵥ (M.β₁ + M.β₂ b))) Fbc)
    (hintc : ∀ s, Integrable (fun x => ginv (s + x ⬝ᵥ (M.β₁ + M.β₂ c))) Fbc)
    (ipda : M.surface ginv (M.μ jac) a =ᵐ[Fa] M'.surface ginv (M'.μ jac) a)
    (ipdc : M.surface ginv (M.μ jac) c =ᵐ[Fc] M'.surface ginv (M'.μ jac) c)
    (agdb : M.armMean ginv (M.μ jbc) Fbc b = M'.armMean ginv (M'.μ jbc) Fbc b)
    (agdc : M.armMean ginv (M.μ jbc) Fbc c = M'.armMean ginv (M'.μ jbc) Fbc c) (α : ℝ) :
    M.surface ginv α a = M'.surface ginv α a ∧ M.surface ginv α b = M'.surface ginv α b := by
  obtain ⟨-, -, h3, h4, h5, h6, h7⟩ :=
    twoStudy_identifiable hmono hra hrc hM hM' hS hS' hintb hintc ipda ipdc agdb agdc
  refine ⟨funext fun x => ?_, funext fun x => ?_⟩ <;>
    simp only [surface, eta_eq_affine, h3, h4, h5, h6, h7]

/-- **The comparator population needs no shared effect modifiers.** Under the hypotheses of
`twoStudy_steps` and an equal aggregate mean of `b` in `jbc`, the marginal effect of `b` against
`a` on any scale `g` in the population of the aggregate study (covariate law `F_bc`, baseline
`μ_jbc`) is the same for the two models: the mean of `b` is observed and the surface of `a` uses
only identified parameters. The surfaces of `a` (of `M`) and of `b` (of both models) are
integrable under `F_bc`, so that the arm means compared are genuine means; the surface of `a`
of `M'` is then the same function as that of `M`. The equality itself does not use these
integrability hypotheses. -/
theorem twoStudy_comparator_identified (hmono : StrictMono ginv) [IsProbabilityMeasure Fbc]
    (hra : AffineRank Fa) (hrc : AffineRank Fc) (hM : M.IsAnchoredAt c)
    (hM' : M'.IsAnchoredAt c)
    (hintc : ∀ s, Integrable (fun x => ginv (s + x ⬝ᵥ (M.β₁ + M.β₂ c))) Fbc)
    (_hia : Integrable (M.surface ginv (M.μ jbc) a) Fbc)
    (_hib : Integrable (M.surface ginv (M.μ jbc) b) Fbc)
    (_hib' : Integrable (M'.surface ginv (M'.μ jbc) b) Fbc)
    (ipda : M.surface ginv (M.μ jac) a =ᵐ[Fa] M'.surface ginv (M'.μ jac) a)
    (ipdc : M.surface ginv (M.μ jac) c =ᵐ[Fc] M'.surface ginv (M'.μ jac) c)
    (agdb : M.armMean ginv (M.μ jbc) Fbc b = M'.armMean ginv (M'.μ jbc) Fbc b)
    (agdc : M.armMean ginv (M.μ jbc) Fbc c = M'.armMean ginv (M'.μ jbc) Fbc c) (g : ℝ → ℝ) :
    linkMarginal g Fbc (M.surface ginv (M.μ jbc) a) (M.surface ginv (M.μ jbc) b) =
      linkMarginal g Fbc (M'.surface ginv (M'.μ jbc) a) (M'.surface ginv (M'.μ jbc) b) := by
  obtain ⟨-, h2, h3, h4, h5⟩ := twoStudy_steps hmono hra hrc hM hM' hintc ipda ipdc agdc
  have hsa : M.surface ginv (M.μ jbc) a = M'.surface ginv (M'.μ jbc) a := funext fun x => by
    simp only [surface, eta_eq_affine, h2, h3, h4, h5]
  change g (M.armMean ginv (M.μ jbc) Fbc b) - g (∫ x, M.surface ginv (M.μ jbc) a x ∂Fbc) =
    g (M'.armMean ginv (M'.μ jbc) Fbc b) - g (∫ x, M'.surface ginv (M'.μ jbc) a x ∂Fbc)
  rw [agdb, hsa]

end MultilevelModel

/-! ### Failure models -/

section Failure

open MultilevelModel

/-- The **triangle model** with one covariate: treatments `0 = a`, `1 = b`, `2 = c` (anchored at
`2`), studies `0 = jac`, `1 = jbc`, intercepts `μ₀, μ₁`, prognostic effect `β`, effects `γa, γb`
and interactions `δa, δb`. -/
def triangleModel (μ₀ μ₁ β γa γb δa δb : ℝ) : MultilevelModel (Fin 2) (Fin 3) 1 where
  μ := ![μ₀, μ₁]
  β₁ := fun _ => β
  γ := ![γa, γb, 0]
  β₂ := ![fun _ => δa, fun _ => δb, 0]

theorem triangleModel_anchored (μ₀ μ₁ β γa γb δa δb : ℝ) :
    (triangleModel μ₀ μ₁ β γa γb δa δb).IsAnchoredAt 2 :=
  ⟨rfl, rfl⟩

/-- The triangle model shares the effect modifiers of `a` and `b` exactly when `δa = δb`. -/
theorem triangleModel_shared_iff (μ₀ μ₁ β γa γb δa δb : ℝ) :
    (triangleModel μ₀ μ₁ β γa γb δa δb).SharedEffectModifiers {0, 1} ↔ δa = δb := by
  constructor
  · intro h
    have := congrFun (h 0 (by simp) 1 (by simp)) 0
    simpa [triangleModel, atBaseline] using this
  · rintro rfl s hs t ht
    rcases hs with rfl | rfl <;> rcases ht with rfl | rfl <;> rfl

/-- **Without strict monotonicity nothing is identified**: for the constant inverse link `0` the
models with `γ_a = 0` and `γ_a = 1` (all else zero) give the same surfaces everywhere and the same
aggregate means under every law, though their effects of `a` differ. -/
theorem twoStudy_not_identifiable_const_link (F : Measure (Fin 1 → ℝ)) :
    let M := triangleModel 0 0 0 0 0 0 0
    let M' := triangleModel 0 0 0 1 0 0 0
    (∀ α t, M.surface (fun _ => 0) α t = M'.surface (fun _ => 0) α t) ∧
      (∀ α t, M.armMean (fun _ => 0) α F t = M'.armMean (fun _ => 0) α F t) ∧
      M.γ 0 ≠ M'.γ 0 := by
  refine ⟨fun _ _ => rfl, fun _ _ => rfl, ?_⟩
  simp [triangleModel]

/-- **Without covariate variation the prognostic effect is not identified**: on the identity link
with every covariate law the point mass at `0` (which fails `AffineRank`), the models with
`β₁ = 0` and `β₁ = 1` (all else zero) give equal surfaces almost everywhere and equal aggregate
means of every arm, though their prognostic effects differ. -/
theorem twoStudy_not_identifiable_dirac :
    let M := triangleModel 0 0 0 0 0 0 0
    let M' := triangleModel 0 0 1 0 0 0 0
    (∀ α t, M.surface id α t =ᵐ[Measure.dirac 0] M'.surface id α t) ∧
      (∀ α t, M.armMean id α (Measure.dirac 0) t = M'.armMean id α (Measure.dirac 0) t) ∧
      M.β₁ ≠ M'.β₁ ∧ ¬ AffineRank (Measure.dirac (0 : Fin 1 → ℝ)) := by
  refine ⟨fun α t => ?_, fun α t => ?_, ?_, ?_⟩
  · rw [Filter.EventuallyEq, ae_dirac_eq, Filter.eventually_pure]
    simp [surface, eta, metaRegressionPredictor, triangleModel]
  · simp [armMean, surface, eta, metaRegressionPredictor, triangleModel]
  · intro h
    have := congrFun h 0
    simp [triangleModel] at this
  · intro h
    have := (h 0 (fun _ => 1) (by
      rw [ae_dirac_eq, Filter.eventually_pure]
      simp)).2
    have := congrFun this 0
    simp at this

end Failure

end NetworkMetaRegression

end CausalInference
