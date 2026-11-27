/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.StructuralNested.TwoStageWeibull

/-!
# Two-stage estimation: the Weibull stage one with baseline covariates

The Weibull model of `TwoStageWeibull` has the switch indicator as its only covariate. Here the
model has baseline covariates through a saturated intercept: one intercept `a l` for each
stratum `l` of a finite covariate `L` measured at the secondary baseline, and a common switch
coefficient `b₁`, with linear predictor `a (L) + b₁ X`.

## Main results

* `TwoStageTrial.weibullStrataLogLik`, `TwoStageTrial.weibullStrataScoreA`,
  `TwoStageTrial.weibullStrataScoreB`: the log-likelihood and its scores
  (`TwoStageTrial.hasDerivAt_weibullStrataLogLik_intercept`,
  `TwoStageTrial.hasDerivAt_weibullStrataLogLik`); `TwoStageTrial.WeibullStrataFit`: all
  scores vanish.
* `TwoStageTrial.weibullStrata_coef_eq_neg`: under the structural model in the baseline form,
  mean independence of `(U - S)^k` and the switch within every stratum, positivity in every
  stratum of positive mass and `T > S`, every solution has `b₁ = -ψ`, for every shape `k > 0`.
  The proof: with `z = exp (-k (b₁ + ψ))`, the intercept equations fix each intercept, and the
  switch equation becomes `(z - 1) ∑_l m₁ m₀ / (z m₁ + m₀) = 0` with `m_x` the masses of the
  cells, so `z = 1`.
* `TwoStageTrial.weibullStrata_and_stageOne_root`: under these assumptions and `BaselineNUC`,
  the fit and the stratified mean-balancing `stageOne` return the same parameter, for every
  weight vector `w` that satisfies `BaselinePositive`; the stratum masses qualify
  (`TwoStageTrial.baselinePositive_masses`). The stage-one root does not depend on the weights
  here because each stratum term vanishes at the truth.
* `TwoStageTrial.weibullStrataScoreB_one_eq_stageOne`: without no unmeasured confounding, at
  shape `1` and fitted intercepts, the switch score is `stageOne` at `ψ = -b₁` with the
  weights `expWeight` at `ψ`, which depend on `ψ` and on the outcome. So the exponential fit
  with stratum intercepts is a stratified stage one with moving weights, not one with a fixed
  weight vector.
-/

@[expose] public section

open Finset CausalInference.Longitudinal

namespace CausalInference

namespace StructuralNested

namespace TwoStageTrial

variable {Ω : Type*} (M : TwoStageTrial Ω) [Fintype Ω] [DecidableEq Ω] {𝓛 : Type*} [Fintype 𝓛]
  [DecidableEq 𝓛]

/-- The linear predictor of the log scale with one intercept per stratum and a common switch
coefficient, `a (L) + b₁ X`. -/
noncomputable def strataPredictor (L : Ω → 𝓛) (a : 𝓛 → ℝ) (b₁ : ℝ) (ω : Ω) : ℝ :=
  a (L ω) + b₁ * M.switchCov ω

/-- **The population log-likelihood of the Weibull model with stratum intercepts**: the
log-density `log k - k η + (k - 1) log t - t^k exp (-k η)` of `t = T - S`, with
`η = a (L) + b₁ X`, averaged over `P`. -/
noncomputable def weibullStrataLogLik (p : FiniteDist Ω) (P : Finset Ω) (L : Ω → 𝓛) (k : ℝ)
    (a : 𝓛 → ℝ) (b₁ : ℝ) : ℝ :=
  wsum p P fun ω =>
    Real.log k - k * M.strataPredictor L a b₁ ω + (k - 1) * Real.log (M.T ω - M.S ω) -
      (M.T ω - M.S ω) ^ k * Real.exp (-(k * M.strataPredictor L a b₁ ω))

/-- The score of the intercept of the stratum `l`. -/
noncomputable def weibullStrataScoreA (p : FiniteDist Ω) (P : Finset Ω) (L : Ω → 𝓛) (k : ℝ)
    (a : 𝓛 → ℝ) (b₁ : ℝ) (l : 𝓛) : ℝ :=
  wsum p (P ∩ ev L l) fun ω =>
    k * ((M.T ω - M.S ω) ^ k * Real.exp (-(k * M.strataPredictor L a b₁ ω)) - 1)

/-- The score of the common switch coefficient. -/
noncomputable def weibullStrataScoreB (p : FiniteDist Ω) (P : Finset Ω) (L : Ω → 𝓛) (k : ℝ)
    (a : 𝓛 → ℝ) (b₁ : ℝ) : ℝ :=
  wsum p P fun ω =>
    k * ((M.T ω - M.S ω) ^ k * Real.exp (-(k * M.strataPredictor L a b₁ ω)) - 1) *
      M.switchCov ω

omit [DecidableEq Ω] [Fintype 𝓛] [DecidableEq 𝓛] in
/-- **The switch score is the derivative of the log-likelihood in the switch coefficient.** -/
theorem hasDerivAt_weibullStrataLogLik (p : FiniteDist Ω) (P : Finset Ω) (L : Ω → 𝓛)
    (k : ℝ) (a : 𝓛 → ℝ) (b₁ : ℝ) :
    HasDerivAt (M.weibullStrataLogLik p P L k a) (M.weibullStrataScoreB p P L k a b₁) b₁ := by
  unfold weibullStrataLogLik weibullStrataScoreB wsum
  refine HasDerivAt.fun_sum fun ω _ => ?_
  have hη : HasDerivAt (fun b => M.strataPredictor L a b ω) (M.switchCov ω) b₁ := by
    simpa [strataPredictor] using ((hasDerivAt_id b₁).mul_const (M.switchCov ω)).const_add
      (a (L ω))
  have := (hasDerivAt_weibullTerm hη (Real.log k + (k - 1) * Real.log (M.T ω - M.S ω)) k
    ((M.T ω - M.S ω) ^ k)).const_mul (p ω)
  convert this using 1
  funext b; ring

omit [Fintype 𝓛] in
/-- **The intercept score of a stratum is the derivative of the log-likelihood** in that
intercept. -/
theorem hasDerivAt_weibullStrataLogLik_intercept (p : FiniteDist Ω) (P : Finset Ω)
    (L : Ω → 𝓛) (k : ℝ) (a : 𝓛 → ℝ) (b₁ : ℝ) (l : 𝓛) :
    HasDerivAt (fun c => M.weibullStrataLogLik p P L k (Function.update a l c) b₁)
      (M.weibullStrataScoreA p P L k a b₁ l) (a l) := by
  have e : M.weibullStrataScoreA p P L k a b₁ l = wsum p P fun ω =>
      k * ((M.T ω - M.S ω) ^ k * Real.exp (-(k * M.strataPredictor L a b₁ ω)) - 1) *
        (if L ω = l then 1 else 0) := by
    rw [weibullStrataScoreA, wsum, wsum,
      show P ∩ ev L l = P.filter fun ω => L ω = l by ext; simp [ev], sum_filter]
    exact sum_congr rfl fun ω _ => by split_ifs <;> simp
  rw [e]
  unfold weibullStrataLogLik wsum
  refine HasDerivAt.fun_sum fun ω _ => ?_
  have hη : HasDerivAt (fun c => M.strataPredictor L (Function.update a l c) b₁ ω)
      (if L ω = l then 1 else 0) (a l) := by
    by_cases h : L ω = l
    · simp only [strataPredictor, h, Function.update_self, ite_true]
      exact (hasDerivAt_id (a l)).add_const _
    · simp only [strataPredictor, Function.update_of_ne h, h, ite_false]
      exact hasDerivAt_const _ _
  have h' : M.strataPredictor L (Function.update a l (a l)) b₁ ω = M.strataPredictor L a b₁ ω :=
    by simp
  have := (hasDerivAt_weibullTerm hη (Real.log k + (k - 1) * Real.log (M.T ω - M.S ω)) k
    ((M.T ω - M.S ω) ^ k)).const_mul (p ω)
  rw [h'] at this
  convert this using 1
  funext c; ring

/-- **The Weibull fit with stratum intercepts**: every intercept score and the switch score
vanish. -/
def WeibullStrataFit (p : FiniteDist Ω) (P : Finset Ω) (L : Ω → 𝓛) (k : ℝ) (a : 𝓛 → ℝ)
    (b₁ : ℝ) : Prop :=
  (∀ l, M.weibullStrataScoreA p P L k a b₁ l = 0) ∧ M.weibullStrataScoreB p P L k a b₁ = 0

omit [Fintype 𝓛] in
/-- The score restricted to a cell. -/
theorem wsum_strata_cell (p : FiniteDist Ω) (P : Finset Ω) (L : Ω → 𝓛) (k : ℝ) (a : 𝓛 → ℝ)
    (b₁ : ℝ) (x : Bool) (l : 𝓛) :
    wsum p (M.cell P L x l) (fun ω =>
        k * ((M.T ω - M.S ω) ^ k * Real.exp (-(k * M.strataPredictor L a b₁ ω)) - 1)) =
      k * (Real.exp (-(k * (a l + b₁ * if x then 1 else 0))) *
        wsum p (M.cell P L x l) (fun ω => (M.T ω - M.S ω) ^ k) - wmass p (M.cell P L x l)) := by
  have e : ∀ ω ∈ M.cell P L x l,
      k * ((M.T ω - M.S ω) ^ k * Real.exp (-(k * M.strataPredictor L a b₁ ω)) - 1) =
        k * Real.exp (-(k * (a l + b₁ * if x then 1 else 0))) * (M.T ω - M.S ω) ^ k +
          (-k) * 1 := fun ω hω => by
    simp only [cell, mem_inter, mem_ev] at hω
    simp only [strataPredictor, switchCov, hω.1.2, hω.2]
    ring
  rw [wsum_congr e]
  simp only [wsum, wmass, mul_sub, mul_sum, ← sum_sub_distrib]
  exact sum_congr rfl fun _ _ => by ring

omit [Fintype 𝓛] in
/-- The intercept score of a stratum split over the switch groups. -/
theorem weibullStrataScoreA_eq (p : FiniteDist Ω) (P : Finset Ω) (L : Ω → 𝓛) (k : ℝ)
    (a : 𝓛 → ℝ) (b₁ : ℝ) (l : 𝓛) :
    M.weibullStrataScoreA p P L k a b₁ l =
      k * (Real.exp (-(k * (a l + b₁))) * wsum p (M.cell P L true l)
          (fun ω => (M.T ω - M.S ω) ^ k) - wmass p (M.cell P L true l)) +
        k * (Real.exp (-(k * a l)) * wsum p (M.cell P L false l)
          (fun ω => (M.T ω - M.S ω) ^ k) - wmass p (M.cell P L false l)) := by
  rw [weibullStrataScoreA, wsum_eq_sum_ev (P ∩ ev L l) M.X, Fintype.sum_bool]
  have h1 := M.wsum_strata_cell p P L k a b₁ true l
  have h0 := M.wsum_strata_cell p P L k a b₁ false l
  simp only [ite_true, mul_one, Bool.false_eq_true, ite_false, mul_zero, add_zero] at h1 h0
  exact congrArg₂ (· + ·) h1 h0

/-- The switch score split over the strata: the sum of the switcher terms. -/
theorem weibullStrataScoreB_eq (p : FiniteDist Ω) (P : Finset Ω) (L : Ω → 𝓛) (k : ℝ)
    (a : 𝓛 → ℝ) (b₁ : ℝ) :
    M.weibullStrataScoreB p P L k a b₁ = ∑ l,
      k * (Real.exp (-(k * (a l + b₁))) * wsum p (M.cell P L true l)
          (fun ω => (M.T ω - M.S ω) ^ k) - wmass p (M.cell P L true l)) := by
  rw [weibullStrataScoreB, wsum_eq_sum_ev P L]
  refine sum_congr rfl fun l _ => ?_
  rw [wsum_eq_sum_ev (P ∩ ev L l) M.X, Fintype.sum_bool]
  have h1 := M.wsum_strata_cell p P L k a b₁ true l
  simp only [ite_true, mul_one] at h1
  have c1 : wsum p (P ∩ ev L l ∩ ev M.X true) (fun ω =>
      k * ((M.T ω - M.S ω) ^ k * Real.exp (-(k * M.strataPredictor L a b₁ ω)) - 1) *
        M.switchCov ω) = wsum p (M.cell P L true l) (fun ω =>
      k * ((M.T ω - M.S ω) ^ k * Real.exp (-(k * M.strataPredictor L a b₁ ω)) - 1)) :=
    wsum_congr fun ω hω => by
      have hx : M.X ω = true := mem_ev.1 (mem_inter.1 hω).2
      simp [switchCov, hx]
  have c0 : wsum p (P ∩ ev L l ∩ ev M.X false) (fun ω =>
      k * ((M.T ω - M.S ω) ^ k * Real.exp (-(k * M.strataPredictor L a b₁ ω)) - 1) *
        M.switchCov ω) = 0 := by
    rw [wsum_congr (g := fun _ => 0) fun ω hω => by
      have hx : M.X ω = false := mem_ev.1 (mem_inter.1 hω).2
      simp [switchCov, hx]]
    simp [wsum]
  rw [c1, c0, add_zero, h1]

omit [Fintype 𝓛] in
/-- Under the structural model in the baseline form and `T > S`, the power sum of the
untreated time after the secondary baseline in a cell. -/
theorem wsum_cell_untreated {p : FiniteDist Ω} {P : Finset Ω} {L : Ω → 𝓛} {ψ k : ℝ}
    (hmodel : M.ModelOn P M.S ψ) (htime : ∀ ω ∈ P, M.S ω < M.T ω) (x : Bool) (l : 𝓛) :
    wsum p (M.cell P L x l) (fun ω => (M.U ω - M.S ω) ^ k) =
      (if x then Real.exp (ψ * k) else 1) * wsum p (M.cell P L x l)
        (fun ω => (M.T ω - M.S ω) ^ k) := by
  rw [wsum, wsum, mul_sum]
  refine sum_congr rfl fun ω hω => ?_
  simp only [cell, mem_inter, mem_ev] at hω
  have hP := hω.1.1
  rw [hmodel ω hP]
  cases x
  · rw [M.adjusted_of_not_switch _ _ hω.2]; simp
  · rw [M.adjusted_of_switch _ _ hω.2, add_sub_cancel_left,
      Real.mul_rpow (Real.exp_pos _).le (sub_pos.2 (htime ω hP)).le, ← Real.exp_mul]
    simp only [ite_true]
    ring

omit [Fintype 𝓛] in
/-- **The Weibull fit with stratum intercepts recovers the true time ratio.** Suppose the
structural model holds on `P` in the baseline form, the `k`-th power of the untreated time
after the secondary baseline is mean independent of the switch within every stratum of `L`
(no unmeasured confounding within strata), every stratum of positive mass contains switchers
and non-switchers with positive mass, some stratum has positive mass, and `T > S` on `P`. Then
for every shape `k > 0`, at any solution of the score equations of the Weibull model with one
intercept per stratum and a common switch coefficient, the coefficient is `-ψ`. -/
theorem weibullStrata_coef_eq_neg [Finite 𝓛] {p : FiniteDist Ω} {P : Finset Ω} {L : Ω → 𝓛} {ψ k : ℝ}
    (hk : 0 < k) (hmodel : M.ModelOn P M.S ψ)
    (hnuc : ∀ l, MeanIndepOn p (P ∩ ev L l) (ev M.X true) fun ω => (M.U ω - M.S ω) ^ k)
    (hpos : ∀ l, 0 < wmass p (P ∩ ev L l) →
      0 < wmass p (M.cell P L true l) ∧ 0 < wmass p (M.cell P L false l))
    (hex : ∃ l, 0 < wmass p (P ∩ ev L l)) (htime : ∀ ω ∈ P, M.S ω < M.T ω)
    {a : 𝓛 → ℝ} {b₁ : ℝ} (hfit : M.WeibullStrataFit p P L k a b₁) :
    b₁ = -ψ := by
  have := Fintype.ofFinite 𝓛
  set z := Real.exp (-(k * (b₁ + ψ))) with hz
  have hzpos : 0 < z := Real.exp_pos _
  -- the switcher term of each stratum
  set r : 𝓛 → ℝ := fun l => Real.exp (-(k * (a l + b₁))) *
    wsum p (M.cell P L true l) (fun ω => (M.T ω - M.S ω) ^ k) with hr
  set m1 : 𝓛 → ℝ := fun l => wmass p (M.cell P L true l)
  set m0 : 𝓛 → ℝ := fun l => wmass p (M.cell P L false l)
  set d : 𝓛 → ℝ := fun l => m1 l * m0 l / (z * m1 l + m0 l)
  have key : ∀ l, r l - m1 l = (z - 1) * d l := by
    intro l
    rcases (wmass_nonneg p.nonneg (P ∩ ev L l)).lt_or_eq with hl | hl
    · obtain ⟨h1, h0⟩ := hpos l hl
      set C1 := wsum p (M.cell P L true l) (fun ω => (M.T ω - M.S ω) ^ k)
      set C0 := wsum p (M.cell P L false l) (fun ω => (M.T ω - M.S ω) ^ k)
      have hC0 : 0 < C0 := wsum_pos_of_pos (fun ω hω => Real.rpow_pos_of_pos
        (sub_pos.2 (htime ω (mem_inter.1 (mem_inter.1 hω).1).1)) k) h0
      have heq := M.condMean_switch_eq (hnuc l) h1 h0
      change condMean p (M.cell P L true l) _ = condMean p (M.cell P L false l) _ at heq
      rw [condMean, condMean, M.wsum_cell_untreated hmodel htime true l,
        M.wsum_cell_untreated hmodel htime false l] at heq
      simp only [ite_true, Bool.false_eq_true, ite_false, one_mul] at heq
      have hA := (M.weibullStrataScoreA_eq p P L k a b₁ l).symm.trans (hfit.1 l)
      have hA' : Real.exp (-(k * (a l + b₁))) * C1 - m1 l +
          (Real.exp (-(k * a l)) * C0 - m0 l) = 0 := by
        have := hk.ne'
        rw [← mul_add] at hA
        exact (mul_eq_zero.1 hA).resolve_left this
      have e1 : Real.exp (-(k * (a l + b₁))) = Real.exp (-(k * a l)) * z *
          Real.exp (k * ψ) := by
        rw [hz, ← Real.exp_add, ← Real.exp_add]; congr 1; ring
      have hm1 : 0 < m1 l := h1
      have hm0 : 0 < m0 l := h0
      change Real.exp (-(k * (a l + b₁))) * C1 - m1 l =
        (z - 1) * (m1 l * m0 l / (z * m1 l + m0 l))
      set ν := C0 / m0 l
      have hC0' : C0 = ν * m0 l := by simp only [ν]; field_simp
      have hE1 : Real.exp (k * ψ) * C1 = m1 l * ν := by
        rw [div_eq_iff hm1.ne', mul_comm ψ k] at heq
        linear_combination heq
      rw [e1, hC0'] at hA'
      rw [e1]
      have hden : 0 < z * m1 l + m0 l := by positivity
      rw [mul_div_assoc', eq_div_iff hden.ne']
      linear_combination (z * m1 l) * hA' + (Real.exp (-(k * a l)) * z * m0 l) * hE1
    · have hm1 : m1 l = 0 := le_antisymm (hl ▸ wmass_mono p.nonneg inter_subset_left)
        (wmass_nonneg p.nonneg _)
      have hC1 : wsum p (M.cell P L true l) (fun ω => (M.T ω - M.S ω) ^ k) = 0 :=
        wsum_eq_zero_of_wmass_eq_zero p.nonneg hm1 _
      simp only [r, d, hC1, hm1, mul_zero, zero_mul, zero_div, sub_zero]
  have hB := (M.weibullStrataScoreB_eq p P L k a b₁).symm.trans hfit.2
  rw [← mul_sum] at hB
  have hsum : ∑ l, (r l - m1 l) = 0 := by
    exact (mul_eq_zero.1 hB).resolve_left hk.ne'
  simp only [key, ← mul_sum] at hsum
  have hdpos : 0 < ∑ l, d l := by
    obtain ⟨l₀, hl₀⟩ := hex
    obtain ⟨h1, h0⟩ := hpos l₀ hl₀
    have hd : ∀ l, 0 ≤ d l := fun l => div_nonneg
      (mul_nonneg (wmass_nonneg p.nonneg _) (wmass_nonneg p.nonneg _))
      (add_nonneg (mul_nonneg hzpos.le (wmass_nonneg p.nonneg _)) (wmass_nonneg p.nonneg _))
    exact (sum_pos_iff_of_nonneg fun l _ => hd l).2 ⟨l₀, mem_univ _,
      div_pos (mul_pos h1 h0) (add_pos (mul_pos hzpos h1) h0)⟩
  have hz1 : z = 1 := by
    have := (mul_eq_zero.1 hsum).resolve_right hdpos.ne'
    linarith
  rw [hz, Real.exp_eq_one_iff, neg_eq_zero, mul_eq_zero] at hz1
  rcases hz1 with h | h
  · exact absurd h hk.ne'
  · linarith

/-- **The Weibull fit with stratum intercepts and the stratified mean-balancing stage one have
the same root.** Under the structural model in the baseline form, no unmeasured confounding
within strata for `U - S` (`BaselineNUC`) and for its `k`-th power, positivity in every
stratum of positive mass and `T > S`, the fitted coefficient is `-ψ` and `ψ` is a root of
`stageOne` with the strata `L` for every choice of weights `w` that satisfies positivity
(`BaselinePositive`), in particular the stratum masses. -/
theorem weibullStrata_and_stageOne_root {p : FiniteDist Ω} {P : Finset Ω} {L : Ω → 𝓛}
    {ψ k : ℝ} (hk : 0 < k) (hmodel : M.ModelOn P M.S ψ) (hnuc1 : M.BaselineNUC p P L)
    (hnuc : ∀ l, MeanIndepOn p (P ∩ ev L l) (ev M.X true) fun ω => (M.U ω - M.S ω) ^ k)
    (hpos : ∀ l, 0 < wmass p (P ∩ ev L l) →
      0 < wmass p (M.cell P L true l) ∧ 0 < wmass p (M.cell P L false l))
    (hex : ∃ l, 0 < wmass p (P ∩ ev L l)) (htime : ∀ ω ∈ P, M.S ω < M.T ω)
    {a : 𝓛 → ℝ} {b₁ : ℝ} (hfit : M.WeibullStrataFit p P L k a b₁) {w : 𝓛 → ℝ}
    (hw : M.BaselinePositive p P L w) :
    b₁ = -ψ ∧ M.stageOne p P L w M.S ψ = 0 :=
  ⟨M.weibullStrata_coef_eq_neg hk hmodel hnuc hpos hex htime hfit,
    M.stageOne_eq_zero hmodel hnuc1 hw⟩

omit [Fintype 𝓛] in
/-- The stratum masses satisfy positivity when every stratum of positive mass contains
switchers and non-switchers with positive mass. -/
theorem baselinePositive_masses {p : FiniteDist Ω} {P : Finset Ω} {L : Ω → 𝓛}
    (hpos : ∀ l, 0 < wmass p (P ∩ ev L l) →
      0 < wmass p (M.cell P L true l) ∧ 0 < wmass p (M.cell P L false l)) :
    M.BaselinePositive p P L fun l => wmass p (P ∩ ev L l) := fun l hl =>
  hpos l ((wmass_nonneg p.nonneg _).lt_of_ne (Ne.symm hl))

/-! ### The exponential fit is a stratified stage one with weights that depend on `ψ` -/

/-- The weight of the stratum `l` in the exponential fit at the parameter `ψ`:
`m₁ m₀ / (exp ψ E[T - S ; switchers] + E[T - S ; non-switchers])`, with `m_x` the cell masses
and the sums taken over the cells of `l`. It depends on `ψ` and on the outcome. -/
noncomputable def expWeight (p : FiniteDist Ω) (P : Finset Ω) (L : Ω → 𝓛) (ψ : ℝ) (l : 𝓛) :
    ℝ :=
  wmass p (M.cell P L true l) * wmass p (M.cell P L false l) /
    (Real.exp ψ * wsum p (M.cell P L true l) (fun ω => M.T ω - M.S ω) +
      wsum p (M.cell P L false l) (fun ω => M.T ω - M.S ω))

omit [Fintype 𝓛] in
/-- The transformed residual in the baseline form, summed over a cell. -/
theorem wsum_cell_resid (p : FiniteDist Ω) (P : Finset Ω) (L : Ω → 𝓛) (ψ : ℝ) (x : Bool)
    (l : 𝓛) :
    wsum p (M.cell P L x l) (M.resid M.S ψ) =
      (if x then Real.exp ψ else 1) * wsum p (M.cell P L x l) (fun ω => M.T ω - M.S ω) := by
  rw [wsum, wsum, mul_sum]
  refine sum_congr rfl fun ω hω => ?_
  simp only [cell, mem_inter, mem_ev] at hω
  rw [resid]
  cases x
  · rw [M.adjusted_of_not_switch _ _ hω.2]; simp
  · rw [M.adjusted_of_switch _ _ hω.2]; simp only [ite_true]; ring

/-- **With shape `1`, once the intercepts are fitted, the switch score is the stratified
mean-balancing stage one** at `ψ = -b₁` with the weights `expWeight` at `ψ`, which depend on
`ψ`. No unmeasured confounding is used; the assumptions are positivity in every stratum of
positive mass and `T > S`. So the exponential fit with stratum intercepts has the root of a
stratified `stageOne` whose weights move with `ψ`; a fixed weight vector gives the same root
only under no unmeasured confounding within strata (`weibullStrata_and_stageOne_root`), when
every stratum term vanishes at the truth. -/
theorem weibullStrataScoreB_one_eq_stageOne {p : FiniteDist Ω} {P : Finset Ω} {L : Ω → 𝓛}
    (hpos : ∀ l, 0 < wmass p (P ∩ ev L l) →
      0 < wmass p (M.cell P L true l) ∧ 0 < wmass p (M.cell P L false l))
    (htime : ∀ ω ∈ P, M.S ω < M.T ω) {a : 𝓛 → ℝ} {b₁ : ℝ}
    (hA : ∀ l, M.weibullStrataScoreA p P L 1 a b₁ l = 0) :
    M.weibullStrataScoreB p P L 1 a b₁ =
      M.stageOne p P L (M.expWeight p P L (-b₁)) M.S (-b₁) := by
  rw [weibullStrataScoreB_eq, stageOne]
  refine sum_congr rfl fun l _ => ?_
  simp only [Real.rpow_one, one_mul]
  set C1 := wsum p (M.cell P L true l) (fun ω => M.T ω - M.S ω)
  set C0 := wsum p (M.cell P L false l) (fun ω => M.T ω - M.S ω)
  set m1 := wmass p (M.cell P L true l)
  set m0 := wmass p (M.cell P L false l)
  rw [condMean, condMean, M.wsum_cell_resid, M.wsum_cell_resid]
  simp only [ite_true, Bool.false_eq_true, ite_false, one_mul]
  rcases (wmass_nonneg p.nonneg (P ∩ ev L l)).lt_or_eq with hl | hl
  · obtain ⟨h1, h0⟩ := hpos l hl
    have hC0 : 0 < C0 := wsum_pos_of_pos (fun ω hω =>
      sub_pos.2 (htime ω (mem_inter.1 (mem_inter.1 hω).1).1)) h0
    have hC1 : 0 < C1 := wsum_pos_of_pos (fun ω hω =>
      sub_pos.2 (htime ω (mem_inter.1 (mem_inter.1 hω).1).1)) h1
    have hAl := (M.weibullStrataScoreA_eq p P L 1 a b₁ l).symm.trans (hA l)
    simp only [Real.rpow_one, one_mul] at hAl
    have e1 : Real.exp (-(a l + b₁)) = Real.exp (-a l) * Real.exp (-b₁) := by
      rw [← Real.exp_add]; congr 1; ring
    rw [e1] at hAl ⊢
    have hE : 0 < Real.exp (-b₁) * C1 + C0 := by positivity
    have hm1 : 0 < m1 := h1
    have hm0 : 0 < m0 := h0
    rw [expWeight]
    change Real.exp (-a l) * Real.exp (-b₁) * C1 - m1 =
      m1 * m0 / (Real.exp (-b₁) * C1 + C0) * (Real.exp (-b₁) * C1 / m1 - C0 / m0)
    have hR : m1 * m0 / (Real.exp (-b₁) * C1 + C0) * (Real.exp (-b₁) * C1 / m1 - C0 / m0) =
        (Real.exp (-b₁) * C1 * m0 - C0 * m1) / (Real.exp (-b₁) * C1 + C0) := by
      field_simp
    rw [hR, eq_div_iff hE.ne']
    linear_combination (Real.exp (-b₁) * C1) * hAl
  · have hm1 : m1 = 0 := le_antisymm (hl ▸ wmass_mono p.nonneg inter_subset_left)
      (wmass_nonneg p.nonneg _)
    have hm0 : m0 = 0 := le_antisymm (hl ▸ wmass_mono p.nonneg inter_subset_left)
      (wmass_nonneg p.nonneg _)
    have hC1 : C1 = 0 := wsum_eq_zero_of_wmass_eq_zero p.nonneg hm1 _
    have hC0 : C0 = 0 := wsum_eq_zero_of_wmass_eq_zero p.nonneg hm0 _
    rw [expWeight]
    change _ * C1 - m1 = m1 * m0 / _ * (_ * C1 / m1 - C0 / m0)
    simp [hm1, hm0, hC1, hC0]

end TwoStageTrial

end StructuralNested

end CausalInference
