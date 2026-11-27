/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.StructuralNested.TwoStageLogistic
public import Mathlib.Analysis.Convex.Deriv

/-!
# Two-stage estimation with g-estimation: concavity of the logistic likelihood

The population log-likelihood `SwitchClock.logLik` of the logistic switching model with a
saturated history part is concave jointly in the history intercepts and the coefficient `β` of
the candidate untreated time (`SwitchClock.concaveOn_logLik`). So the score conditions of
`TwoStageLogistic` describe the maximizer.

## Main results

* `SwitchClock.strictConcaveOn_logLikTerm`: one term `a log σ(η) + (1 - a) log (1 - σ(η))` is
  strictly concave in `η`, for every real `a`.
* `SwitchClock.logLik_le_of_fitted`: with the history part at its fitted values `α` at `β = 0`,
  `logLik α' β' ≤ logLik α 0 + β' betaScore α 0` for all `α'`, `β'`.
* `SwitchClock.isMax_of_fitted`, `SwitchClock.exists_max_iff_betaScore`,
  `SwitchClock.exists_max_iff_gEst`: the likelihood has a maximizer with `β = 0` if and only if
  `betaScore` at zero vanishes at the fitted history values, that is if and only if
  `gEst ψ = 0`; and then the fitted values with `β = 0` are a maximizer.
* `SwitchClock.strictConcaveOn_logLik_beta`: uniqueness in `β`. If some patient of positive mass
  at risk at a period before `K` has `U(ψ) ≠ 0`, the log-likelihood is strictly concave in `β`
  for fixed intercepts, so the maximizing `β` is unique. The intercepts are unique only on risk
  cells of positive mass (`Real.sigmoid` is injective); the others do not enter the likelihood.
-/

@[expose] public section

open Finset CausalInference.Longitudinal

namespace CausalInference

namespace StructuralNested

namespace SwitchClock

/-- One term of the log-likelihood as a function of the linear predictor. -/
noncomputable def logLikTerm (a η : ℝ) : ℝ :=
  a * Real.log (Real.sigmoid η) + (1 - a) * Real.log (1 - Real.sigmoid η)

/-- The derivative of one term in the linear predictor is `a - σ(η)`. -/
theorem hasDerivAt_logLikTermη (a η : ℝ) :
    HasDerivAt (logLikTerm a) (a - Real.sigmoid η) η := by
  have := hasDerivAt_logLikTerm a 0 1 η
  simp only [zero_add, mul_one] at this
  exact this

/-- **One term is strictly concave in the linear predictor**, for every real `a`: its
derivative `a - σ(η)` is strictly decreasing. -/
theorem strictConcaveOn_logLikTerm (a : ℝ) : StrictConcaveOn ℝ Set.univ (logLikTerm a) := by
  refine StrictAntiOn.strictConcaveOn_of_deriv convex_univ
    (fun x _ => (hasDerivAt_logLikTermη a x).continuousAt.continuousWithinAt) ?_
  intro x _ y _ hxy
  rw [(hasDerivAt_logLikTermη a x).deriv, (hasDerivAt_logLikTermη a y).deriv]
  linarith [Real.sigmoid_strictMono hxy]

/-- The tangent line of a concave differentiable function lies above it. -/
theorem le_tangent {f : ℝ → ℝ} (hf : ConcaveOn ℝ Set.univ f) {x f' : ℝ}
    (hd : HasDerivAt f f' x) (y : ℝ) : f y ≤ f x + f' * (y - x) := by
  rcases lt_trichotomy x y with hxy | rfl | hxy
  · have := hf.slope_le_of_hasDerivAt (Set.mem_univ x) (Set.mem_univ y) hxy hd
    rw [slope_def_field, div_le_iff₀ (sub_pos.2 hxy)] at this
    linarith
  · simp
  · have := hf.le_slope_of_hasDerivAt (Set.mem_univ y) (Set.mem_univ x) hxy hd
    rw [slope_def_field, le_div_iff₀ (sub_pos.2 hxy)] at this
    linarith

variable {Ω 𝓗 : Type*} (M : SwitchClock Ω 𝓗) [Fintype Ω] [DecidableEq Ω] [DecidableEq 𝓗]

omit [DecidableEq 𝓗] in
/-- The log-likelihood as a sum of terms in the linear predictor. -/
theorem logLik_eq (p : FiniteDist Ω) (K : ℕ) (ψ : ℝ) (α : ℕ → 𝓗 → ℝ) (β : ℝ) :
    M.logLik p K ψ α β = ∑ j ∈ range K,
      wsum p (M.riskSet j) fun ω => logLikTerm (M.switchInd j ω) (M.predictor ψ α β j ω) :=
  rfl

omit [DecidableEq 𝓗] in
/-- **The log-likelihood is concave jointly in the history intercepts and `β`.** -/
theorem concaveOn_logLik (p : FiniteDist Ω) (K : ℕ) (ψ : ℝ) :
    ConcaveOn ℝ Set.univ fun x : (ℕ → 𝓗 → ℝ) × ℝ => M.logLik p K ψ x.1 x.2 := by
  refine ⟨convex_univ, fun x _ y _ a b ha hb hab => ?_⟩
  simp only [logLik_eq, wsum, smul_eq_mul, mul_sum, ← sum_add_distrib]
  refine sum_le_sum fun j _ => sum_le_sum fun ω _ => ?_
  have hpred : M.predictor ψ (a • x + b • y).1 (a • x + b • y).2 j ω =
      a • M.predictor ψ x.1 x.2 j ω + b • M.predictor ψ y.1 y.2 j ω := by
    simp only [predictor, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, Pi.add_apply,
      Pi.smul_apply, smul_eq_mul]
    ring
  have hc := (strictConcaveOn_logLikTerm (M.switchInd j ω)).concaveOn.2
    (Set.mem_univ (M.predictor ψ x.1 x.2 j ω)) (Set.mem_univ (M.predictor ψ y.1 y.2 j ω)) ha hb hab
  rw [hpred]
  simp only [smul_eq_mul] at hc ⊢
  nlinarith [p.nonneg ω, mul_le_mul_of_nonneg_left hc (p.nonneg ω)]

/-- With the history part fitted, the score of a history direction vanishes in every
period. -/
theorem wsum_alpha_direction {p : FiniteDist Ω} {K : ℕ} {α : ℕ → 𝓗 → ℝ} (hα : M.Fitted p K α)
    (ψ : ℝ) (δ : ℕ → 𝓗 → ℝ) {j : ℕ} (hj : j < K) :
    wsum p (M.riskSet j) (fun ω =>
      (M.switchInd j ω - Real.sigmoid (α j (M.H j ω))) * δ j (M.H j ω)) = 0 := by
  rw [wsum, ← sum_fiberwise_of_maps_to (g := M.H j) (t := (M.riskSet j).image (M.H j))
    fun ω hω => mem_image_of_mem _ hω]
  refine sum_eq_zero fun h _ => ?_
  have hc : (M.riskSet j).filter (fun ω => M.H j ω = h) = M.riskSet j ∩ ev (M.H j) h := by
    ext ω; simp [ev]
  rw [hc, ← wsum]
  have e : wsum p (M.riskSet j ∩ ev (M.H j) h) (fun ω =>
      (M.switchInd j ω - Real.sigmoid (α j (M.H j ω))) * δ j (M.H j ω)) =
      δ j h * M.alphaScore p ψ α 0 j h := by
    rw [alphaScore, wsum, wsum, mul_sum]
    refine sum_congr rfl fun ω hω => ?_
    have : M.H j ω = h := mem_ev.1 (mem_inter.1 hω).2
    rw [this, zero_mul, add_zero]
    ring
  rw [e]
  by_cases hm : 0 < wmass p (M.riskCell j h)
  · rw [(M.alphaScore_zero_iff p ψ α j h hm).2 (hα j hj h hm), mul_zero]
  · have h0 : wmass p (M.riskCell j h) = 0 :=
      le_antisymm (not_lt.1 hm) (sum_nonneg fun ω _ => p.nonneg ω)
    rw [alphaScore, wsum_eq_zero_of_wmass_eq_zero p.nonneg h0, mul_zero]

/-- **The tangent bound at the fitted values.** With the history part at its fitted values `α`
at `β = 0`, `logLik α' β' ≤ logLik α 0 + β' betaScore α 0` for all intercepts `α'` and all
`β'`. -/
theorem logLik_le_of_fitted {p : FiniteDist Ω} {K : ℕ} {α : ℕ → 𝓗 → ℝ} (hα : M.Fitted p K α)
    (ψ : ℝ) (α' : ℕ → 𝓗 → ℝ) (β' : ℝ) :
    M.logLik p K ψ α' β' ≤ M.logLik p K ψ α 0 + β' * M.betaScore p K ψ α 0 := by
  have key : ∀ j ∈ range K, wsum p (M.riskSet j)
      (fun ω => logLikTerm (M.switchInd j ω) (M.predictor ψ α' β' j ω)) ≤
      wsum p (M.riskSet j)
        (fun ω => logLikTerm (M.switchInd j ω) (M.predictor ψ α 0 j ω)) +
      β' * wsum p (M.riskSet j) (fun ω =>
        (M.switchInd j ω - Real.sigmoid (M.predictor ψ α 0 j ω)) * M.counterfactual ψ ω) :=
    fun j hj => by
      have hz := M.wsum_alpha_direction hα ψ (fun j h => α' j h - α j h) (mem_range.1 hj)
      have hle : wsum p (M.riskSet j)
          (fun ω => logLikTerm (M.switchInd j ω) (M.predictor ψ α' β' j ω)) ≤
          wsum p (M.riskSet j) (fun ω =>
            logLikTerm (M.switchInd j ω) (M.predictor ψ α 0 j ω) +
              (M.switchInd j ω - Real.sigmoid (α j (M.H j ω))) * (α' j (M.H j ω) - α j (M.H j ω))
              + β' * ((M.switchInd j ω - Real.sigmoid (M.predictor ψ α 0 j ω)) *
                M.counterfactual ψ ω)) := by
        refine sum_le_sum fun ω _ => mul_le_mul_of_nonneg_left ?_ (p.nonneg ω)
        have ht := le_tangent (strictConcaveOn_logLikTerm (M.switchInd j ω)).concaveOn
          (hasDerivAt_logLikTermη (M.switchInd j ω) (M.predictor ψ α 0 j ω))
          (M.predictor ψ α' β' j ω)
        simp only [predictor, zero_mul, add_zero] at ht ⊢
        linarith
      have hsplit : wsum p (M.riskSet j) (fun ω =>
            logLikTerm (M.switchInd j ω) (M.predictor ψ α 0 j ω) +
              (M.switchInd j ω - Real.sigmoid (α j (M.H j ω))) * (α' j (M.H j ω) - α j (M.H j ω))
              + β' * ((M.switchInd j ω - Real.sigmoid (M.predictor ψ α 0 j ω)) *
                M.counterfactual ψ ω)) =
          wsum p (M.riskSet j)
            (fun ω => logLikTerm (M.switchInd j ω) (M.predictor ψ α 0 j ω)) +
          wsum p (M.riskSet j) (fun ω => (M.switchInd j ω - Real.sigmoid (α j (M.H j ω))) *
            (α' j (M.H j ω) - α j (M.H j ω))) +
          β' * wsum p (M.riskSet j) (fun ω =>
            (M.switchInd j ω - Real.sigmoid (M.predictor ψ α 0 j ω)) * M.counterfactual ψ ω) := by
        simp only [wsum, mul_add, sum_add_distrib, mul_sum]
        congr 1
        exact sum_congr rfl fun _ _ => by ring
      rw [hsplit, hz, add_zero] at hle
      exact hle
  rw [logLik_eq, logLik_eq, betaScore, mul_sum, ← sum_add_distrib]
  exact sum_le_sum key

/-- **The fitted values with `β = 0` maximize the likelihood when the score of `β` vanishes
there.** -/
theorem isMax_of_fitted {p : FiniteDist Ω} {K : ℕ} {α : ℕ → 𝓗 → ℝ} (hα : M.Fitted p K α)
    {ψ : ℝ} (hβ : M.betaScore p K ψ α 0 = 0) (α' : ℕ → 𝓗 → ℝ) (β' : ℝ) :
    M.logLik p K ψ α' β' ≤ M.logLik p K ψ α 0 := by
  have := M.logLik_le_of_fitted hα ψ α' β'
  rwa [hβ, mul_zero, add_zero] at this

/-- **The maximizer has `β = 0` exactly when `betaScore` at zero vanishes at the fitted history
values.** For fitted `α`, some `α₁` with `β = 0` maximizes the log-likelihood if and only if
`betaScore α 0 = 0`. -/
theorem exists_max_iff_betaScore {p : FiniteDist Ω} {K : ℕ} {α : ℕ → 𝓗 → ℝ}
    (hα : M.Fitted p K α) (ψ : ℝ) :
    (∃ α₁ : ℕ → 𝓗 → ℝ, ∀ α' β', M.logLik p K ψ α' β' ≤ M.logLik p K ψ α₁ 0) ↔
      M.betaScore p K ψ α 0 = 0 := by
  constructor
  · rintro ⟨α₁, h₁⟩
    have hmax : IsMaxOn (M.logLik p K ψ α) Set.univ 0 := fun β _ => by
      have := M.logLik_le_of_fitted hα ψ α₁ 0
      rw [zero_mul, add_zero] at this
      exact (h₁ α β).trans this
    exact (hmax.isLocalMax Filter.univ_mem).hasDerivAt_eq_zero (M.hasDerivAt_logLik p K ψ α 0)
  · intro hβ
    exact ⟨α, M.isMax_of_fitted hα hβ⟩

/-- **The same condition as `gEst ψ = 0`.** -/
theorem exists_max_iff_gEst {p : FiniteDist Ω} {K : ℕ} {α : ℕ → 𝓗 → ℝ}
    (hα : M.Fitted p K α) (ψ : ℝ) :
    (∃ α₁ : ℕ → 𝓗 → ℝ, ∀ α' β', M.logLik p K ψ α' β' ≤ M.logLik p K ψ α₁ 0) ↔
      M.gEst p K ψ = 0 := by
  rw [M.exists_max_iff_betaScore hα, M.betaScore_eq_zero_iff hα]

omit [DecidableEq 𝓗] in
/-- **Strict concavity in `β`.** If some patient of positive mass at risk at a period before
`K` has `U(ψ) ≠ 0`, the log-likelihood is strictly concave in `β` for fixed intercepts; so its
maximizer in `β` is unique. -/
theorem strictConcaveOn_logLik_beta {p : FiniteDist Ω} {K : ℕ} {ψ : ℝ} (α : ℕ → 𝓗 → ℝ)
    (h : ∃ j < K, ∃ ω ∈ M.riskSet j, 0 < p ω ∧ M.counterfactual ψ ω ≠ 0) :
    StrictConcaveOn ℝ Set.univ (M.logLik p K ψ α) := by
  obtain ⟨j₀, hj₀, ω₀, hω₀, hp, hu⟩ := h
  refine ⟨convex_univ, fun x _ y _ hxy a b ha hb hab => ?_⟩
  simp only [logLik_eq, wsum, smul_eq_mul, mul_sum, ← sum_add_distrib]
  have term : ∀ j ω, a * (p ω * logLikTerm (M.switchInd j ω) (M.predictor ψ α x j ω)) +
      b * (p ω * logLikTerm (M.switchInd j ω) (M.predictor ψ α y j ω)) ≤
      p ω * logLikTerm (M.switchInd j ω) (M.predictor ψ α (a * x + b * y) j ω) := fun j ω => by
    have hpred : M.predictor ψ α (a * x + b * y) j ω =
        a • M.predictor ψ α x j ω + b • M.predictor ψ α y j ω := by
      simp only [predictor, smul_eq_mul]
      linear_combination (-(α j (M.H j ω))) * hab
    have hc := (strictConcaveOn_logLikTerm (M.switchInd j ω)).concaveOn.2
      (Set.mem_univ (M.predictor ψ α x j ω)) (Set.mem_univ (M.predictor ψ α y j ω)) ha.le hb.le hab
    rw [hpred]
    simp only [smul_eq_mul] at hc ⊢
    nlinarith [p.nonneg ω, mul_le_mul_of_nonneg_left hc (p.nonneg ω)]
  refine sum_lt_sum (fun j _ => sum_le_sum fun ω _ => term j ω)
    ⟨j₀, mem_range.2 hj₀, sum_lt_sum (fun ω _ => term j₀ ω) ⟨ω₀, hω₀, ?_⟩⟩
  have hne : M.predictor ψ α x j₀ ω₀ ≠ M.predictor ψ α y j₀ ω₀ := by
    simp only [predictor, ne_eq, add_right_inj, mul_eq_mul_right_iff, not_or]
    exact ⟨hxy, hu⟩
  have hpred : M.predictor ψ α (a * x + b * y) j₀ ω₀ =
      a • M.predictor ψ α x j₀ ω₀ + b • M.predictor ψ α y j₀ ω₀ := by
    simp only [predictor, smul_eq_mul]
    linear_combination (-(α j₀ (M.H j₀ ω₀))) * hab
  have hs := (strictConcaveOn_logLikTerm (M.switchInd j₀ ω₀)).2
    (Set.mem_univ (M.predictor ψ α x j₀ ω₀)) (Set.mem_univ (M.predictor ψ α y j₀ ω₀)) hne ha hb hab
  rw [hpred]
  simp only [smul_eq_mul] at hs ⊢
  nlinarith [mul_lt_mul_of_pos_left hs hp]

end SwitchClock

end StructuralNested

end CausalInference
