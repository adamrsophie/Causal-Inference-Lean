/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.StructuralNested.TwoStageGEstimation
public import Mathlib.Analysis.SpecialFunctions.Sigmoid
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# Two-stage estimation with g-estimation: the logistic switching model

TSD 24, Section 4.2.3.1 ("TSE with g-estimation") fits a model for switching given the measured
history with the counterfactual survival `U(ψ)` as an added covariate, and takes as estimate
the `ψ` at which that covariate has coefficient zero. This file links the logistic form of that
model to the covariance form `SwitchClock.gEst`.

The model: at period `j`, for a patient at risk with history `h`,
`P(switch at j) = σ(α j h + β U(ψ))`, with `σ = Real.sigmoid`. The history part is saturated:
one intercept `α j h` for each period and history value.

## Main results

* `SwitchClock.logLik`: the population log-likelihood of the model, summed over periods and
  risk sets; `SwitchClock.hasDerivAt_logLik`: its derivative in `β` is the score
  `SwitchClock.betaScore`, `∑_j ∑_{at risk} p (A_j - σ(α + β U(ψ))) U(ψ)`.
* `SwitchClock.alphaScore`, `SwitchClock.alphaScore_zero_iff`: at `β = 0` the score of the
  intercept of a risk cell of positive mass vanishes if and only if `σ(α j h)` is the switch
  proportion of that cell. These are the fitted values of the history part at `β = 0`
  (`SwitchClock.Fitted`), which exist when every such proportion is strictly between `0` and
  `1` (`SwitchClock.exists_fitted_all`).
* `SwitchClock.betaScore_zero_eq_gEst`: at `β = 0` and the fitted values of the history part,
  the score for the coefficient of `U(ψ)` is `gEst ψ`; so `SwitchClock.betaScore_eq_zero_iff`:
  the score for that coefficient vanishes at zero exactly when `gEst ψ = 0`.

The statement is about the score at `β = 0`, the population condition behind "coefficient
zero"; that the maximizer of the likelihood has `β = 0` exactly when this score vanishes
(concavity of the logistic log-likelihood) is not formalized here.
-/

@[expose] public section

open Finset CausalInference.Longitudinal

namespace CausalInference

namespace StructuralNested

namespace SwitchClock

variable {Ω 𝓗 : Type*} (M : SwitchClock Ω 𝓗) [Fintype Ω] [DecidableEq Ω] [DecidableEq 𝓗]

/-- The linear predictor of the logistic switching model for `ω` at period `j`. -/
noncomputable def predictor (ψ : ℝ) (α : ℕ → 𝓗 → ℝ) (β : ℝ) (j : ℕ) (ω : Ω) : ℝ :=
  α j (M.H j ω) + β * M.counterfactual ψ ω

/-- **The population log-likelihood of the logistic switching model** with the candidate
untreated time `U(ψ)` as covariate: `∑_{j < K} ∑_{at risk at j} p (A_j log σ(η) +
(1 - A_j) log (1 - σ(η)))`. -/
noncomputable def logLik (p : FiniteDist Ω) (K : ℕ) (ψ : ℝ) (α : ℕ → 𝓗 → ℝ) (β : ℝ) : ℝ :=
  ∑ j ∈ range K, wsum p (M.riskSet j) fun ω =>
    M.switchInd j ω * Real.log (Real.sigmoid (M.predictor ψ α β j ω)) +
      (1 - M.switchInd j ω) * Real.log (1 - Real.sigmoid (M.predictor ψ α β j ω))

/-- **The score for the coefficient of `U(ψ)`**:
`∑_{j < K} ∑_{at risk at j} p (A_j - σ(η)) U(ψ)`. -/
noncomputable def betaScore (p : FiniteDist Ω) (K : ℕ) (ψ : ℝ) (α : ℕ → 𝓗 → ℝ) (β : ℝ) : ℝ :=
  ∑ j ∈ range K, wsum p (M.riskSet j) fun ω =>
    (M.switchInd j ω - Real.sigmoid (M.predictor ψ α β j ω)) * M.counterfactual ψ ω

/-- One term of the log-likelihood has derivative `(a - σ(c + β u)) u` in `β`. -/
theorem hasDerivAt_logLikTerm (a c u β : ℝ) :
    HasDerivAt (fun b => a * Real.log (Real.sigmoid (c + b * u)) +
        (1 - a) * Real.log (1 - Real.sigmoid (c + b * u)))
      ((a - Real.sigmoid (c + β * u)) * u) β := by
  have hlin : HasDerivAt (fun b : ℝ => c + b * u) u β := by
    simpa using ((hasDerivAt_id β).mul_const u).const_add c
  have hs : HasDerivAt (fun b => Real.sigmoid (c + b * u))
      (Real.sigmoid (c + β * u) * (1 - Real.sigmoid (c + β * u)) * u) β := by
    have := (Real.hasDerivAt_sigmoid (c + β * u)).comp β hlin
    exact this
  have hpos := Real.sigmoid_pos (c + β * u)
  have hne : 1 - Real.sigmoid (c + β * u) ≠ 0 := by linarith [Real.sigmoid_lt_one (c + β * u)]
  have h1 := (hs.log hpos.ne').const_mul a
  have h2 := ((hs.const_sub 1).log hne).const_mul (1 - a)
  convert h1.add h2 using 1
  field_simp
  ring

omit [DecidableEq 𝓗] in
/-- **The derivative of the log-likelihood in `β` is the score `betaScore`.** -/
theorem hasDerivAt_logLik (p : FiniteDist Ω) (K : ℕ) (ψ : ℝ) (α : ℕ → 𝓗 → ℝ) (β : ℝ) :
    HasDerivAt (M.logLik p K ψ α) (M.betaScore p K ψ α β) β := by
  unfold logLik betaScore wsum
  refine HasDerivAt.fun_sum fun j _ => HasDerivAt.fun_sum fun ω _ => ?_
  exact (hasDerivAt_logLikTerm (M.switchInd j ω) (α j (M.H j ω)) (M.counterfactual ψ ω) β
    |>.const_mul (p ω))

/-- The score for the intercept of the risk cell of period `j` and history `h`:
`∑_{risk cell} p (A_j - σ(α j h + β U(ψ)))`. -/
noncomputable def alphaScore (p : FiniteDist Ω) (ψ : ℝ) (α : ℕ → 𝓗 → ℝ) (β : ℝ) (j : ℕ)
    (h : 𝓗) : ℝ :=
  wsum p (M.riskCell j h) fun ω =>
    M.switchInd j ω - Real.sigmoid (α j h + β * M.counterfactual ψ ω)

/-- **At `β = 0` the intercept score of a cell of positive mass vanishes exactly at the switch
proportion of the cell.** -/
theorem alphaScore_zero_iff (p : FiniteDist Ω) (ψ : ℝ) (α : ℕ → 𝓗 → ℝ) (j : ℕ) (h : 𝓗)
    (hm : 0 < wmass p (M.riskCell j h)) :
    M.alphaScore p ψ α 0 j h = 0 ↔
      Real.sigmoid (α j h) = condProb p (M.riskCell j h) (M.switchAt j) := by
  have e : M.alphaScore p ψ α 0 j h =
      wmass p (M.riskCell j h ∩ M.switchAt j) -
        Real.sigmoid (α j h) * wmass p (M.riskCell j h) := by
    simp only [alphaScore, zero_mul, add_zero, wsum, wmass, mul_sub, sum_sub_distrib, mul_sum]
    congr 1
    · simp only [switchInd, mul_ite, mul_one, mul_zero]
      rw [← sum_filter, filter_mem_eq_inter]
    · exact sum_congr rfl fun _ _ => by ring
  rw [e, condProb, sub_eq_zero, eq_div_iff hm.ne', eq_comm]

/-- **The fitted values of the saturated history part at `β = 0`**: in every risk cell of
positive mass before `K`, `σ(α j h)` is the switch proportion of the cell, the root of the
intercept score (`alphaScore_zero_iff`). -/
def Fitted (p : FiniteDist Ω) (K : ℕ) (α : ℕ → 𝓗 → ℝ) : Prop :=
  ∀ j < K, ∀ h, 0 < wmass p (M.riskCell j h) →
    Real.sigmoid (α j h) = condProb p (M.riskCell j h) (M.switchAt j)

/-- A fitted intercept exists for a switch proportion strictly between `0` and `1`. -/
theorem exists_fitted {q : ℝ} (h0 : 0 < q) (h1 : q < 1) : ∃ a, Real.sigmoid a = q := by
  have : q ∈ Set.range Real.sigmoid := by rw [Real.range_sigmoid]; exact ⟨h0, h1⟩
  exact this

/-- **Fitted values exist** when the switch proportion of every risk cell of positive mass
before `K` is strictly between `0` and `1`. -/
theorem exists_fitted_all {p : FiniteDist Ω} {K : ℕ}
    (h : ∀ j < K, ∀ h, 0 < wmass p (M.riskCell j h) →
      0 < condProb p (M.riskCell j h) (M.switchAt j) ∧
        condProb p (M.riskCell j h) (M.switchAt j) < 1) :
    ∃ α, M.Fitted p K α := by
  classical
  refine ⟨fun j g => if hc : j < K ∧ 0 < wmass p (M.riskCell j g) then
    Classical.choose (exists_fitted (h j hc.1 g hc.2).1 (h j hc.1 g hc.2).2) else 0, ?_⟩
  intro j hj g hm
  simp only [hj, hm, and_self, dite_true]
  exact Classical.choose_spec (exists_fitted (h j hj g hm).1 (h j hj g hm).2)

/-- **The score for the coefficient of `U(ψ)` at zero, with the history part at its fitted
values, is the covariance form of the g-estimating function.** -/
theorem betaScore_zero_eq_gEst {p : FiniteDist Ω} {K : ℕ} {α : ℕ → 𝓗 → ℝ}
    (hα : M.Fitted p K α) (ψ : ℝ) : M.betaScore p K ψ α 0 = M.gEst p K ψ := by
  refine sum_congr rfl fun j hj => wsum_congr_of_ne_zero fun ω hω h0 => ?_
  have hpos : 0 < p ω := (p.nonneg ω).lt_of_ne (Ne.symm h0)
  have hcell : ω ∈ M.riskCell j (M.H j ω) := mem_inter.2 ⟨hω, mem_ev.2 rfl⟩
  have hfit := hα j (mem_range.1 hj) (M.H j ω) (wmass_pos_of_mem p.nonneg hcell hpos)
  simp only [predictor, zero_mul, add_zero, hfit]
  rfl

/-- **"Coefficient zero" and `gEst = 0` are the same population condition**: with the history
part at its fitted values, the score for the coefficient of `U(ψ)` vanishes at zero if and only
if `gEst ψ = 0`. With `SwitchClock.gEst_eq_zero_iff`, under the structural model, sequential no
unmeasured confounding and relevance this happens exactly at the true parameter. -/
theorem betaScore_eq_zero_iff {p : FiniteDist Ω} {K : ℕ} {α : ℕ → 𝓗 → ℝ}
    (hα : M.Fitted p K α) (ψ : ℝ) : M.betaScore p K ψ α 0 = 0 ↔ M.gEst p K ψ = 0 := by
  rw [M.betaScore_zero_eq_gEst hα]

end SwitchClock

end StructuralNested

end CausalInference
