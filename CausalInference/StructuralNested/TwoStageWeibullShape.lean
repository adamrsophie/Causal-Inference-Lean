/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.StructuralNested.TwoStageWeibull
public import CausalInference.StructuralNested.TwoStageTwoArm
public import CausalInference.StructuralNested.IPECensoring
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-!
# Two-stage estimation: the Weibull stage one with the shape estimated

The fit of `TwoStageWeibull` takes the shape `k` as given. Here the shape is estimated too: the
full fit solves three score equations.

## Main results

* `TwoStageTrial.weibullScoreShape`, `TwoStageTrial.hasDerivAt_weibullLogLik_shape`: the score
  of the shape is the derivative of `weibullLogLik` in `k`, for `k > 0` and `T > S`.
* `TwoStageTrial.WeibullFullFit`: the intercept, switch and shape scores vanish.
  `TwoStageTrial.weibullFullFit_coef_eq_neg`: any solution with a positive shape has
  coefficient `-ψ`, from `weibull_coef_eq_neg` at the fitted shape;
  `TwoStageTrial.weibullFullFit_coef_eq_neg_of_condIndep`: the distributional form of no
  unmeasured confounding covers every shape.
* `TwoStageTrial.weibullScoreShape_eq_profile`: at the fitted intercept and coefficient for a
  shape, the shape score is the profile score `weibullProfile`, the mass weighted sum over the
  switch groups of `1/k + E[log t] - E[t^k log t] / E[t^k]`.
* `TwoStageTrial.shapeScore_groupTrial`: the profile score is `SwitchingTrial.shapeScore` of
  `IPECensoring` for the trial `groupTrial` whose arms are the switch groups and whose time is
  `T - S` with no time on treatment. The argument transfers:
  `TwoStageTrial.exists_weibullFullFit` (existence, from `SwitchingTrial.exists_shapeScore_root`)
  and `TwoStageTrial.weibullFullFit_unique` (uniqueness, from
  `SwitchingTrial.shapeScore_strictAntiOn`), on all patients (`P = univ`) with `T > S`
  everywhere and both groups of positive mass; existence also needs two patients of positive
  mass in one switch group with different times. What differs from `IPECensoring`: the arms
  there are randomized arms and here they are switch groups, the time there is the candidate
  untreated time and here it is `T - S`, and its hypotheses are measure theoretic; on a finite
  law they reduce to the conditions above.
-/

@[expose] public section

open Finset MeasureTheory ProbabilityTheory CausalInference.Longitudinal

namespace CausalInference

namespace StructuralNested

namespace TwoStageTrial

variable {Ω : Type*} (M : TwoStageTrial Ω) [Fintype Ω] [DecidableEq Ω]

/-- **The score of the shape `k`** of the Weibull log-likelihood `weibullLogLik`:
`E[1/k - η + log t - t^k exp (-k η) (log t - η) ; P]`, with `t = T - S` and
`η = b₀ + b₁ X`. -/
noncomputable def weibullScoreShape (p : FiniteDist Ω) (P : Finset Ω) (k b₀ b₁ : ℝ) : ℝ :=
  wsum p P fun ω =>
    1 / k - M.weibullPredictor b₀ b₁ ω + Real.log (M.T ω - M.S ω) -
      (M.T ω - M.S ω) ^ k * Real.exp (-(k * M.weibullPredictor b₀ b₁ ω)) *
        (Real.log (M.T ω - M.S ω) - M.weibullPredictor b₀ b₁ ω)

omit [DecidableEq Ω] in
/-- **The shape score is the derivative of the log-likelihood in the shape**, for `k > 0` and
`T > S` on `P`. -/
theorem hasDerivAt_weibullLogLik_shape (p : FiniteDist Ω) (P : Finset Ω) {k : ℝ} (hk : 0 < k)
    (htime : ∀ ω ∈ P, M.S ω < M.T ω) (b₀ b₁ : ℝ) :
    HasDerivAt (fun k => M.weibullLogLik p P k b₀ b₁) (M.weibullScoreShape p P k b₀ b₁) k := by
  unfold weibullLogLik weibullScoreShape wsum
  refine HasDerivAt.fun_sum fun ω hω => ?_
  have ht : 0 < M.T ω - M.S ω := sub_pos.2 (htime ω hω)
  set η := M.weibullPredictor b₀ b₁ ω
  set t := M.T ω - M.S ω
  have hl := Real.hasDerivAt_log hk.ne'
  have hlin := (hasDerivAt_id k).mul_const η
  have hlog := ((hasDerivAt_id k).sub_const 1).mul_const (Real.log t)
  have hpow := (Real.hasStrictDerivAt_const_rpow ht k).hasDerivAt
  have hexp := hlin.neg.exp
  have hall := ((hl.sub hlin).add hlog).sub (hpow.mul hexp)
  have := hall.const_mul (p ω)
  convert this using 1
  · funext k
    simp only [Pi.sub_apply, Pi.add_apply, Pi.mul_apply, Pi.neg_apply, id, η, t]
  · simp only [id, Pi.neg_apply]
    field_simp
    ring

/-- **The full Weibull fit**: the three score equations, intercept, switch coefficient and
shape. -/
def WeibullFullFit (p : FiniteDist Ω) (P : Finset Ω) (k b₀ b₁ : ℝ) : Prop :=
  M.weibullScore₀ p P k b₀ b₁ = 0 ∧ M.weibullScore₁ p P k b₀ b₁ = 0 ∧
    M.weibullScoreShape p P k b₀ b₁ = 0

/-- **Any solution of the full score system with a positive shape has coefficient `-ψ`**,
under the assumptions of `weibull_coef_eq_neg` at the fitted shape. -/
theorem weibullFullFit_coef_eq_neg {p : FiniteDist Ω} {P : Finset Ω} {ψ k : ℝ} (hk : 0 < k)
    (hmodel : M.ModelOn P M.S ψ)
    (hnuc : MeanIndepOn p P (ev M.X true) fun ω => (M.U ω - M.S ω) ^ k)
    (h1 : 0 < wmass p (P ∩ ev M.X true)) (h0 : 0 < wmass p (P ∩ ev M.X false))
    (htime : ∀ ω ∈ P, M.S ω < M.T ω) {b₀ b₁ : ℝ} (hfit : M.WeibullFullFit p P k b₀ b₁) :
    b₁ = -ψ :=
  M.weibull_coef_eq_neg hk hmodel hnuc h1 h0 htime ⟨hfit.1, hfit.2.1⟩

/-- The same under no unmeasured confounding in distributional form, which holds at every
shape, so whatever shape the full fit returns. -/
theorem weibullFullFit_coef_eq_neg_of_condIndep {p : FiniteDist Ω} {P : Finset Ω} {ψ k : ℝ}
    (hk : 0 < k) (hmodel : M.ModelOn P M.S ψ) (hci : M.BaselineCondIndep p P fun _ => ())
    (h1 : 0 < wmass p (P ∩ ev M.X true)) (h0 : 0 < wmass p (P ∩ ev M.X false))
    (htime : ∀ ω ∈ P, M.S ω < M.T ω) {b₀ b₁ : ℝ} (hfit : M.WeibullFullFit p P k b₀ b₁) :
    b₁ = -ψ :=
  M.weibullFullFit_coef_eq_neg hk hmodel (M.weibull_nuc_of_condIndep hci k) h1 h0 htime hfit

/-! ### The profile shape score -/

/-- The profile shape score of the switch group `x`:
`1/k + E[log t | x] - E[t^k log t | x] / E[t^k | x]`, with `t = T - S`. -/
noncomputable def profileArm (p : FiniteDist Ω) (P : Finset Ω) (k : ℝ) (x : Bool) : ℝ :=
  1 / k + condMean p (P ∩ ev M.X x) (fun ω => Real.log (M.T ω - M.S ω)) -
    condMean p (P ∩ ev M.X x) (fun ω => (M.T ω - M.S ω) ^ k * Real.log (M.T ω - M.S ω)) /
      M.powerMean p P k x

/-- **The profile shape score**: the shape score at the fitted intercept and coefficient for
the shape `k`, the mass weighted sum of the profile scores of the two switch groups. -/
noncomputable def weibullProfile (p : FiniteDist Ω) (P : Finset Ω) (k : ℝ) : ℝ :=
  ∑ x : Bool, wmass p (P ∩ ev M.X x) * M.profileArm p P k x

/-- The shape score restricted to a group on which the linear predictor is the constant `c`,
with `exp (k c)` the power mean of the group. -/
theorem wsum_shape_group (p : FiniteDist Ω) (P : Finset Ω) {k b₀ b₁ c : ℝ} (x : Bool)
    (hη : ∀ ω ∈ P ∩ ev M.X x, M.weibullPredictor b₀ b₁ ω = c)
    (hm : Real.exp (k * c) = M.powerMean p P k x) (hs : 0 < wmass p (P ∩ ev M.X x)) :
    wsum p (P ∩ ev M.X x) (fun ω =>
      1 / k - M.weibullPredictor b₀ b₁ ω + Real.log (M.T ω - M.S ω) -
        (M.T ω - M.S ω) ^ k * Real.exp (-(k * M.weibullPredictor b₀ b₁ ω)) *
          (Real.log (M.T ω - M.S ω) - M.weibullPredictor b₀ b₁ ω)) =
      wmass p (P ∩ ev M.X x) * M.profileArm p P k x := by
  simp only [profileArm, powerMean, condMean] at hm ⊢
  set s := P ∩ ev M.X x
  set W := wmass p s
  set A := wsum p s fun ω => Real.log (M.T ω - M.S ω)
  set Bq := wsum p s fun ω => (M.T ω - M.S ω) ^ k * Real.log (M.T ω - M.S ω)
  set Cq := wsum p s fun ω => (M.T ω - M.S ω) ^ k
  have hlin : wsum p s (fun ω =>
      1 / k - M.weibullPredictor b₀ b₁ ω + Real.log (M.T ω - M.S ω) -
        (M.T ω - M.S ω) ^ k * Real.exp (-(k * M.weibullPredictor b₀ b₁ ω)) *
          (Real.log (M.T ω - M.S ω) - M.weibullPredictor b₀ b₁ ω)) =
      (1 / k - c) * W + A - Real.exp (-(k * c)) * Bq + Real.exp (-(k * c)) * c * Cq := by
    rw [wsum_congr fun ω hω => by rw [hη ω hω]]
    simp only [W, A, Bq, Cq, wsum, wmass, mul_sum, ← sum_add_distrib, ← sum_sub_distrib]
    exact sum_congr rfl fun ω _ => by ring
  have hCpos : 0 < Cq := by
    have := hm ▸ Real.exp_pos (k * c)
    exact (div_pos_iff_of_pos_right hs).1 this
  rw [hlin, Real.exp_neg, hm]
  field_simp
  ring

/-- **At the fitted intercept and coefficient, the shape score is the profile score.** For a
shape `k ≠ 0` and both switch groups of positive mass, if the intercept and the switch scores
vanish then the shape score is `weibullProfile`. -/
theorem weibullScoreShape_eq_profile (p : FiniteDist Ω) (P : Finset Ω) {k : ℝ} (hk : k ≠ 0)
    (h1 : 0 < wmass p (P ∩ ev M.X true)) (h0 : 0 < wmass p (P ∩ ev M.X false)) {b₀ b₁ : ℝ}
    (hfit : M.weibullScore₀ p P k b₀ b₁ = 0 ∧ M.weibullScore₁ p P k b₀ b₁ = 0) :
    M.weibullScoreShape p P k b₀ b₁ = M.weibullProfile p P k := by
  obtain ⟨e0, e1⟩ := (M.weibullScores_eq_zero_iff p P hk h1 h0 b₀ b₁).1 hfit
  rw [weibullScoreShape, wsum_eq_sum_ev P M.X, weibullProfile]
  simp only [Fintype.sum_bool]
  rw [M.wsum_shape_group p P true (c := b₀ + b₁) (fun ω hω => by
      simp [weibullPredictor, switchCov, mem_ev.1 (mem_inter.1 hω).2]) e1 h1,
    M.wsum_shape_group p P false (c := b₀) (fun ω hω => by
      simp [weibullPredictor, switchCov, mem_ev.1 (mem_inter.1 hω).2]) e0 h0]

/-! ### Existence and uniqueness through the shape score of `IPECensoring` -/

/-- The switching trial whose arms are the switch groups and whose time is the time after the
secondary baseline, with no time on treatment: its candidate untreated time is `T - S` at
every `ψ`. -/
def groupTrial : SwitchingTrial Ω where
  R := M.X
  T ω := M.T ω - M.S ω
  Te _ := 0
  U ω := M.U ω - M.S ω

omit [Fintype Ω] [DecidableEq Ω] in
theorem counterfactual_groupTrial (ψ : ℝ) :
    M.groupTrial.counterfactual ψ = M.groupTrial.T := by
  funext ω; simp [SwitchingTrial.counterfactual, SwitchingTrial.Tc, groupTrial]

/-- **The profile shape score is the pooled shape score of `IPECensoring`** for the trial whose
arms are the switch groups. -/
theorem shapeScore_groupTrial [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
    (p : FiniteDist Ω) (ψ k : ℝ) :
    M.groupTrial.shapeScore p.toMeasure ψ k = M.weibullProfile p univ k := by
  have harm : ∀ x, M.groupTrial.arm x = ↑(ev M.X x) := fun x => by
    ext ω; simp [SwitchingTrial.arm, groupTrial]
  have hint : ∀ x (f : Ω → ℝ), ∫ ω, f ω ∂(p.toMeasure[|M.groupTrial.arm x]) =
      condMean p (univ ∩ ev M.X x) f := fun x f => by
    rw [univ_inter]
    exact SwitchingTrial.armMean_toMeasure p M.groupTrial f x
  have hreal : ∀ x, p.toMeasure.real (M.groupTrial.arm x) = wmass p (univ ∩ ev M.X x) :=
    fun x => by rw [harm, univ_inter]; exact p.toMeasure_real_finset _
  rw [SwitchingTrial.shapeScore, counterfactual_groupTrial, weibullProfile, Fintype.sum_bool,
    hreal, hreal]
  simp only [shapeScoreArm, hint, profileArm, powerMean]
  rfl

omit [DecidableEq Ω] in
/-- The hypotheses of the shape score results of `IPECensoring` for the group trial on a
finite law. -/
theorem groupTrial_hyps [MeasurableSpace Ω] [MeasurableSingletonClass Ω] (p : FiniteDist Ω)
    (htime : ∀ ω, M.S ω < M.T ω) :
    M.groupTrial.WellFormed ∧ (∀ ω, 0 < M.groupTrial.T ω) ∧
      ∀ (x : Bool) (f : Ω → ℝ), Integrable f (p.toMeasure[|M.groupTrial.arm x]) := by
  refine ⟨⟨fun _ => le_rfl, fun ω => (sub_pos.2 (htime ω)).le⟩, fun ω => sub_pos.2 (htime ω),
    fun x f => Integrable.of_finite⟩

/-- A group of positive mass has positive measure. -/
theorem groupTrial_arm_ne_zero [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
    {p : FiniteDist Ω} {x : Bool} (h : 0 < wmass p (univ ∩ ev M.X x)) :
    p.toMeasure (M.groupTrial.arm x) ≠ 0 := by
  intro h0
  have harm : M.groupTrial.arm x = ↑(ev M.X x) := by
    ext ω; simp [SwitchingTrial.arm, groupTrial]
  have := p.toMeasure_real_finset (ev M.X x)
  rw [← harm, h0, ENNReal.toReal_zero] at this
  have hw : wmass p (univ ∩ ev M.X x) = p.prob (ev M.X x) := by rw [univ_inter]; rfl
  linarith

/-- The fit from a shape: at the shape `k ≠ 0`, the intercept `log m₀ / k` and the
coefficient `log (m₁ / m₀) / k`, with `m_x` the power means, solve the intercept and switch
score equations. -/
theorem weibullScores_of_shape (p : FiniteDist Ω) (P : Finset Ω) {k : ℝ} (hk : k ≠ 0)
    (h1 : 0 < wmass p (P ∩ ev M.X true)) (h0 : 0 < wmass p (P ∩ ev M.X false))
    (htime : ∀ ω ∈ P, M.S ω < M.T ω) :
    M.weibullScore₀ p P k (Real.log (M.powerMean p P k false) / k)
        (Real.log (M.powerMean p P k true / M.powerMean p P k false) / k) = 0 ∧
      M.weibullScore₁ p P k (Real.log (M.powerMean p P k false) / k)
        (Real.log (M.powerMean p P k true / M.powerMean p P k false) / k) = 0 := by
  have hpos : ∀ x, 0 < wmass p (P ∩ ev M.X x) → 0 < M.powerMean p P k x := fun x hm => by
    rw [powerMean, condMean]
    exact div_pos (wsum_pos_of_pos (fun ω hω => Real.rpow_pos_of_pos
      (sub_pos.2 (htime ω (mem_inter.1 hω).1)) k) hm) hm
  have p1 := hpos true h1
  have p0 := hpos false h0
  refine (M.weibullScores_eq_zero_iff p P hk h1 h0 _ _).2 ⟨?_, ?_⟩
  · rw [mul_div_cancel₀ _ hk, Real.exp_log p0]
  · rw [← add_div, mul_div_cancel₀ _ hk, ← Real.log_mul p0.ne' (div_pos p1 p0).ne',
      mul_div_cancel₀ _ p0.ne', Real.exp_log p1]

/-- **Existence of a solution of the full score system.** On all patients (`P = univ`), with
`T > S` everywhere, both switch groups of positive mass, and two patients of positive mass in
the same switch group with different times after the secondary baseline, the three score
equations have a solution with a positive shape. The proof transfers
`SwitchingTrial.exists_shapeScore_root` through `shapeScore_groupTrial` and
`weibullScoreShape_eq_profile`. -/
theorem exists_weibullFullFit {p : FiniteDist Ω} (htime : ∀ ω, M.S ω < M.T ω)
    (h1 : 0 < wmass p (univ ∩ ev M.X true)) (h0 : 0 < wmass p (univ ∩ ev M.X false))
    (hnc : ∃ ω ω', M.X ω = M.X ω' ∧ 0 < p ω ∧ 0 < p ω' ∧
      M.T ω - M.S ω ≠ M.T ω' - M.S ω') :
    ∃ k b₀ b₁, 0 < k ∧ M.WeibullFullFit p univ k b₀ b₁ := by
  let _ : MeasurableSpace Ω := ⊤
  have _ : MeasurableSingletonClass Ω := ⟨fun _ => MeasurableSpace.measurableSet_top⟩
  obtain ⟨hwf, hT, hI⟩ := M.groupTrial_hyps p htime
  have hnc' : ∀ x, (∃ ω ω', M.X ω = x ∧ M.X ω' = x ∧ 0 < p ω ∧ 0 < p ω' ∧
      M.T ω - M.S ω ≠ M.T ω' - M.S ω') →
      ¬ ∃ c, ∀ᵐ ω ∂p.toMeasure[|M.groupTrial.arm x], M.groupTrial.T ω = c := by
    rintro x ⟨ω, ω', hx, hx', hp, hp', hne⟩ ⟨c, hc⟩
    have hnull := ae_iff.1 hc
    have hpt : ∀ y, M.X y = x → 0 < p y → M.groupTrial.T y = c := fun y hy hpy => by
      by_contra hyc
      have h0' : p.toMeasure[|M.groupTrial.arm x] {y} = 0 :=
        measure_mono_null (Set.singleton_subset_iff.2 hyc) hnull
      rw [ProbabilityTheory.cond_apply (MeasurableSpace.measurableSet_top),
        Set.inter_eq_right.2 (Set.singleton_subset_iff.2 (by
          simp [SwitchingTrial.arm, groupTrial, hy]))] at h0'
      rcases mul_eq_zero.1 h0' with h | h
      · exact ENNReal.inv_ne_zero.2 (measure_ne_top _ _) h
      · have := p.toMeasure_real_finset {y}
        rw [Finset.coe_singleton, h, ENNReal.toReal_zero] at this
        have hw : p.prob {y} = p y := by
          rw [show p.prob {y} = wmass p {y} from rfl, wmass, sum_singleton]
        linarith
    exact hne ((hpt ω hx hp).trans (hpt ω' hx' hp').symm)
  obtain ⟨ω, ω', hxx, hp, hp', hne⟩ := hnc
  have hnc2 : (¬ ∃ c, ∀ᵐ ω ∂p.toMeasure[|M.groupTrial.arm true], M.groupTrial.T ω = c) ∨
      ¬ ∃ c, ∀ᵐ ω ∂p.toMeasure[|M.groupTrial.arm false],
        M.groupTrial.counterfactual 0 ω = c := by
    rw [counterfactual_groupTrial]
    cases hX : M.X ω
    · exact Or.inr (hnc' false ⟨ω, ω', hX, hxx ▸ hX, hp, hp', hne⟩)
    · exact Or.inl (hnc' true ⟨ω, ω', hX, hxx ▸ hX, hp, hp', hne⟩)
  obtain ⟨k, hk, hroot⟩ := SwitchingTrial.exists_shapeScore_root hwf hT
    (M.groupTrial_arm_ne_zero h1) (M.groupTrial_arm_ne_zero h0) 0
    (fun _ _ => ⟨hI _ _, hI _ _⟩) (fun _ _ => ⟨hI _ _, hI _ _⟩) (hI _ _) (hI _ _) hnc2
  have hs := M.weibullScores_of_shape p univ hk.ne' h1 h0 fun ω _ => htime ω
  refine ⟨k, _, _, hk, hs.1, hs.2, ?_⟩
  rw [M.weibullScoreShape_eq_profile p univ hk.ne' h1 h0 hs, ← M.shapeScore_groupTrial p 0 k,
    hroot]

/-- **Uniqueness of the solution of the full score system** with a positive shape, on all
patients, with `T > S` everywhere and both switch groups of positive mass: the shape is unique
by `SwitchingTrial.shapeScore_strictAntiOn`, and the intercept and the coefficient are then
determined by the power means. -/
theorem weibullFullFit_unique {p : FiniteDist Ω} (htime : ∀ ω, M.S ω < M.T ω)
    (h1 : 0 < wmass p (univ ∩ ev M.X true)) (h0 : 0 < wmass p (univ ∩ ev M.X false))
    {k b₀ b₁ k' b₀' b₁' : ℝ} (hk : 0 < k) (hk' : 0 < k')
    (hfit : M.WeibullFullFit p univ k b₀ b₁) (hfit' : M.WeibullFullFit p univ k' b₀' b₁') :
    k = k' ∧ b₀ = b₀' ∧ b₁ = b₁' := by
  let _ : MeasurableSpace Ω := ⊤
  have _ : MeasurableSingletonClass Ω := ⟨fun _ => MeasurableSpace.measurableSet_top⟩
  obtain ⟨hwf, hT, hI⟩ := M.groupTrial_hyps p htime
  have hanti := SwitchingTrial.shapeScore_strictAntiOn hwf hT (M.groupTrial_arm_ne_zero h1)
    (M.groupTrial_arm_ne_zero h0) 0 (fun _ _ => ⟨hI _ _, hI _ _⟩) (fun _ _ => ⟨hI _ _, hI _ _⟩)
  have e : ∀ {k b₀ b₁ : ℝ}, 0 < k → M.WeibullFullFit p univ k b₀ b₁ →
      M.groupTrial.shapeScore p.toMeasure 0 k = 0 := fun hk hfit => by
    rw [M.shapeScore_groupTrial, ← M.weibullScoreShape_eq_profile p univ hk.ne' h1 h0
      ⟨hfit.1, hfit.2.1⟩]
    exact hfit.2.2
  have hkk : k = k' := hanti.injOn hk hk' ((e hk hfit).trans (e hk' hfit').symm)
  subst hkk
  obtain ⟨a, b⟩ := (M.weibullScores_eq_zero_iff p univ hk.ne' h1 h0 b₀ b₁).1
    ⟨hfit.1, hfit.2.1⟩
  obtain ⟨a', b'⟩ := (M.weibullScores_eq_zero_iff p univ hk.ne' h1 h0 b₀' b₁').1
    ⟨hfit'.1, hfit'.2.1⟩
  have q0 : k * b₀ = k * b₀' := Real.exp_injective (a.trans a'.symm)
  have q1 : k * (b₀ + b₁) = k * (b₀' + b₁') := Real.exp_injective (b.trans b'.symm)
  have r0 : b₀ = b₀' := mul_left_cancel₀ hk.ne' q0
  refine ⟨rfl, r0, ?_⟩
  have := mul_left_cancel₀ hk.ne' q1
  linarith

end TwoStageTrial

end StructuralNested

end CausalInference
