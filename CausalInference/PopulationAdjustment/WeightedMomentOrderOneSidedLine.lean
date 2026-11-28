/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.PopulationAdjustment.WeightedMomentOrderOneSided

/-!
# One sided moments for a scalar feature and the exponential law

For a scalar feature, write `g = X - t`. The consistency theorem under one sided moments
(`sampleBalancedArmMean_isConsistent_trial_of_isMinOn_oneSided`) assumes
`E[exp(s |g|)] < ∞` for some `s > 0` and the directional moment
`E[exp(2 (1 + ε) β* g)] < ∞` for some `ε > 0`. This file relates these hypotheses to a finite
moment generating function near `β*`, `E[exp((β* ± r) g)] < ∞` for some `r > 0`:

* **two points control an interval**: `exp(βg) ≤ exp(ag) + exp(bg)` for `a ≤ β ≤ b`
  (`exp_mul_le_exp_mul_add_exp_mul`, `integrable_exp_mul_of_mem_Icc`);
* **the moment generating function near `β*` follows from the two hypotheses**
  (`exists_integrable_exp_mul_pm_of_oneSided`), so it is not assumed;
* **the small two sided moment follows from the moment generating function near `β*` when
  `β* - r < 0 < β* + r`** (`integrable_exp_abs_of_integrable_exp_mul_pm`).

**The exponential law.** For the standard exponential law and `0 < t`, `β* = 1 - 1/t`. The
moment `E[exp(s |X - t|)]` is finite for `s = 1/2`, and the directional moment
`E[exp(c β* (X - t))]` is finite exactly when `c β* < 1`
(`integrable_exp_directional_momentOrderExpLaw_iff`). Hence both hypotheses hold for every
`0 < t < 2` (`oneSided_hypotheses_momentOrderExpLaw`), and the weighted arm mean of the coin
trial with `Y(true) = 1 + 2X` is consistent for `1 + 2t` (`momentOrderInst_oneSided_consistent`).
The theorem under a directional moment needs a norm moment of order `κ > |β*|`, which exists only
for `t > 1/2`; at `t = 1/3`, `β* = -2`, no such order exists
(`not_exists_order_directional_momentOrderExpLaw_one_third`) while the weighted arm mean
converges to `5/3` (`momentOrderInst_oneSided_one_third`). For `t ≥ 2` the directional moment
is infinite for every `ε > 0` (`not_integrable_directional_momentOrderExpLaw`).

## Main results

* `exp_mul_le_exp_mul_add_exp_mul`, `integrable_exp_mul_of_mem_Icc`,
  `exists_integrable_exp_mul_pm_of_oneSided`, `integrable_exp_abs_of_integrable_exp_mul_pm`.
* `momentOrderInst_consistent_of_isMinOn_oneSided`.
* `integrable_exp_mul_sub_expMeasure`, `exists_integrable_exp_mul_pm_expMeasure_one_third`,
  `integrable_exp_abs_expMeasure_three_halves`.
* `integrable_exp_directional_momentOrderExpLaw_iff`, `oneSided_hypotheses_momentOrderExpLaw`,
  `momentOrderInst_oneSided_consistent`, `not_exists_order_directional_momentOrderExpLaw_one_third`,
  `momentOrderInst_oneSided_one_third`, `not_integrable_directional_momentOrderExpLaw`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Finset
open scoped Topology ENNReal

namespace CausalInference

namespace PopulationAdjustment

open PointTreatment IndirectComparison

/-! ### Scalar moments -/

section Scalar

/-- **Two points control an interval**: `exp(βy) ≤ exp(ay) + exp(by)` for `a ≤ β ≤ b`. -/
theorem exp_mul_le_exp_mul_add_exp_mul {a β b : ℝ} (ha : a ≤ β) (hb : β ≤ b) (y : ℝ) :
    Real.exp (β * y) ≤ Real.exp (a * y) + Real.exp (b * y) := by
  rcases le_total 0 y with hy | hy
  · have := Real.exp_le_exp.2 (mul_le_mul_of_nonneg_right hb hy)
    linarith [Real.exp_pos (a * y)]
  · have := Real.exp_le_exp.2 (mul_le_mul_of_nonpos_right ha hy)
    linarith [Real.exp_pos (b * y)]

variable {𝒪 : Type*} [MeasurableSpace 𝒪] {ν : Measure 𝒪} {g : 𝒪 → ℝ}

/-- `exp(βg)` is integrable when `exp(ag)` and `exp(bg)` are, for `a ≤ β ≤ b`. -/
theorem integrable_exp_mul_of_mem_Icc (hg : Measurable g) {a β b : ℝ} (ha : a ≤ β) (hb : β ≤ b)
    (hia : Integrable (fun z => Real.exp (a * g z)) ν)
    (hib : Integrable (fun z => Real.exp (b * g z)) ν) :
    Integrable (fun z => Real.exp (β * g z)) ν :=
  (hia.add hib).mono' (Real.measurable_exp.comp (measurable_const.mul hg)).aestronglyMeasurable
    (ae_of_all _ fun z => by
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      exact exp_mul_le_exp_mul_add_exp_mul ha hb (g z))

/-- `exp(±s g)` is integrable when `exp(s |g|)` is. -/
theorem integrable_exp_mul_of_integrable_exp_abs (hg : Measurable g) {s : ℝ}
    (hexp : Integrable (fun z => Real.exp (s * |g z|)) ν) {c : ℝ} (hc : |c| ≤ s) :
    Integrable (fun z => Real.exp (c * g z)) ν :=
  hexp.mono' (Real.measurable_exp.comp (measurable_const.mul hg)).aestronglyMeasurable
    (ae_of_all _ fun z => by
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      refine Real.exp_le_exp.2 ((le_abs_self _).trans ?_)
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_right hc (abs_nonneg _))

/-- **The moment generating function near `β*` follows from the one sided hypotheses.** If
`E[exp(s |g|)] < ∞` for some `s > 0` and `E[exp(2 (1 + ε) β g)] < ∞` for some `ε > 0`, then
`E[exp((β - r) g)] < ∞` and `E[exp((β + r) g)] < ∞` for some `r > 0`. -/
theorem exists_integrable_exp_mul_pm_of_oneSided (hg : Measurable g) {s : ℝ} (hs : 0 < s)
    (hexp : Integrable (fun z => Real.exp (s * |g z|)) ν) {ε β : ℝ} (hε : 0 < ε)
    (hdir : Integrable (fun z => Real.exp (2 * (1 + ε) * β * g z)) ν) :
    ∃ r, 0 < r ∧ Integrable (fun z => Real.exp ((β - r) * g z)) ν ∧
      Integrable (fun z => Real.exp ((β + r) * g z)) ν := by
  set c := 2 * (1 + ε) * β with hc
  set a := min (-s) c with ha
  set b := max s c with hb
  have hia : Integrable (fun z => Real.exp (a * g z)) ν := by
    rcases min_choice (-s) c with h | h <;> rw [ha, h]
    · exact integrable_exp_mul_of_integrable_exp_abs hg hexp (by rw [abs_neg, abs_of_pos hs])
    · exact hdir
  have hib : Integrable (fun z => Real.exp (b * g z)) ν := by
    rcases max_choice s c with h | h <;> rw [hb, h]
    · exact integrable_exp_mul_of_integrable_exp_abs hg hexp (by rw [abs_of_pos hs])
    · exact hdir
  have haβ : a < β := by
    rcases le_or_gt 0 β with h | h
    · exact (min_le_left _ _).trans_lt (by linarith)
    · refine (min_le_right _ _).trans_lt ?_
      rw [hc]; nlinarith
  have hbβ : β < b := by
    rcases le_or_gt β 0 with h | h
    · exact lt_of_lt_of_le (by linarith) (le_max_left _ _)
    · refine lt_of_lt_of_le ?_ (le_max_right _ _)
      rw [hc]; nlinarith
  have hr0 : 0 < min (β - a) (b - β) := lt_min (by linarith) (by linarith)
  have h1 := min_le_left (β - a) (b - β)
  have h2 := min_le_right (β - a) (b - β)
  refine ⟨min (β - a) (b - β), hr0, ?_, ?_⟩
  · exact integrable_exp_mul_of_mem_Icc hg (by linarith) (by linarith) hia hib
  · exact integrable_exp_mul_of_mem_Icc hg (by linarith) (by linarith) hia hib

/-- **The small two sided moment follows from the moment generating function near `β*` when
`β* - r < 0 < β* + r`**: with `s = min (r - β) (β + r) > 0`, `E[exp(s |g|)] < ∞`. -/
theorem integrable_exp_abs_of_integrable_exp_mul_pm (hg : Measurable g) {β r : ℝ}
    (hlo : β - r < 0) (hhi : 0 < β + r)
    (hm : Integrable (fun z => Real.exp ((β - r) * g z)) ν)
    (hp : Integrable (fun z => Real.exp ((β + r) * g z)) ν) :
    0 < min (r - β) (β + r) ∧
      Integrable (fun z => Real.exp (min (r - β) (β + r) * |g z|)) ν := by
  set s := min (r - β) (β + r) with hs
  have hs0 : 0 < s := lt_min (by linarith) hhi
  have h1 := integrable_exp_mul_of_mem_Icc (β := s) hg
    (by linarith [min_le_left (r - β) (β + r)]) (min_le_right _ _) hm hp
  have h2 := integrable_exp_mul_of_mem_Icc (β := -s) hg
    (by linarith [min_le_left (r - β) (β + r)]) (by linarith) hm hp
  refine ⟨hs0, (h1.add h2).mono'
    (Real.measurable_exp.comp
      (measurable_const.mul (continuous_abs.measurable.comp hg))).aestronglyMeasurable
    (ae_of_all _ fun z => ?_)⟩
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  simp only [Pi.add_apply]
  rcases abs_cases (g z) with ⟨h, -⟩ | ⟨h, -⟩
  · rw [h]; linarith [Real.exp_pos (-s * g z)]
  · rw [h, mul_neg, ← neg_mul]; linarith [Real.exp_pos (s * g z)]

end Scalar

/-! ### The coin trial under one sided moments -/

section CoinTrial

variable {p : ℕ} {lam : Measure (Fin p → ℝ)} {f : Bool → (Fin p → ℝ) → ℝ}

/-- **Consistency in the coin trial under one sided moments.** For a feature law `lam` with `t`
in the interior of the closed convex hull of its support, a minimizer `β*` of
`E[exp(βᵀ(y - t))]`, `E[exp(s ‖y - t‖)] < ∞` for some `s > 0`,
`E[exp(2 (1 + ε) β*ᵀ(y - t))] < ∞` for some `ε > 0`, measurable outcome functions and the outcome
of arm `a` affine in the features, the weighted arm mean of the records of the coin trial at
targets `tₙ → t` is consistent for `c + dᵀt`. -/
theorem momentOrderInst_consistent_of_isMinOn_oneSided [IsProbabilityMeasure lam]
    (hf : ∀ a, Measurable (f a)) {t : Fin p → ℝ}
    (hint : t ∈ interior (closedConvexHull ℝ lam.support))
    {βs : Fin p → ℝ} (hmin : IsMinOn (sharpDualObjective lam id t) Set.univ βs)
    {s : ℝ} (hs : 0 < s) (hexp : Integrable (fun y => Real.exp (s * ‖y - t‖)) lam)
    {ε : ℝ} (hε : 0 < ε)
    (hdir : Integrable (fun y => Real.exp (2 * (1 + ε) * (βs ⬝ᵥ (y - t)))) lam)
    {tn : ℕ → Fin p → ℝ} (htn : Tendsto tn atTop (𝓝 t)) (a : Bool) {c : ℝ} {d : Fin p → ℝ}
    (haff : ∀ x, f a x = c + d ⬝ᵥ x) :
    IsConsistent (fun n ω => sampleBalancedArmMean id (tn n) (sharpInstSample lam f) a n ω)
      (c + d ⬝ᵥ t) (sharpInstLaw lam f) := by
  have hfi : Integrable (f a) lam := by
    rw [show f a = fun x => c + d ⬝ᵥ x from funext haff]
    exact integrable_affine_of_integrable_exp_pos hs hexp c d
  obtain ⟨hX, hA, hYo, hYa, hrand, hq, hm, hres2, hvar⟩ := sharpInstTrial_hypotheses hf a hfi
  exact sampleBalancedArmMean_isConsistent_trial_of_isMinOn_oneSided hX hA hYo a hYa hrand
    (isIIDSample_sharpInstSample hf) (measurable_sharpInstSample hf) (map_sharpInstSample hf 0)
    measurable_id (t := t) (by rw [Measure.map_id, sharpInstTrial_covLaw]; exact hint)
    (by rw [sharpInstTrial_covLaw]; exact hmin) hs (by rw [sharpInstTrial_covLaw]; exact hexp)
    hε (by rw [sharpInstTrial_covLaw]; exact hdir)
    (W := fun _ => ()) measurable_const
    (indepFun_const_left _ _) (G := fun n _ => tn n) (fun _ => measurable_const)
    (tendstoInMeasure_of_tendsto_ae (fun _ => aestronglyMeasurable_const)
      (ae_of_all _ fun _ => htn)) hq hm hres2 hvar (a0 := c) (b := d) haff

end CoinTrial

/-! ### The exponential law -/

section Exponential

/-- **The directional moments of the exponential feature law**: `E[exp(c βᵀ(X - t))] < ∞`
exactly when `c β < 1`. -/
theorem integrable_exp_directional_momentOrderExpLaw_iff (t c : ℝ) (β : Fin 1 → ℝ) :
    Integrable (fun y => Real.exp (c * (β ⬝ᵥ (y - featureLineVec t)))) momentOrderExpLaw ↔
      c * β 0 < 1 := by
  have hm : Measurable fun y : Fin 1 → ℝ => Real.exp (c * (β ⬝ᵥ (y - featureLineVec t))) := by
    fun_prop
  rw [momentOrderExpLaw, integrable_map_measure hm.aestronglyMeasurable
    measurable_featureLineVec.aemeasurable]
  have e : (fun y : Fin 1 → ℝ => Real.exp (c * (β ⬝ᵥ (y - featureLineVec t)))) ∘
      featureLineVec = fun x => Real.exp (-(c * β 0 * t)) * Real.exp ((c * β 0) * x) := by
    funext x
    simp only [Function.comp_apply, dotProduct_featureLineVec_sub]
    rw [← Real.exp_add]; ring_nf
  rw [e, integrable_const_mul_iff (isUnit_iff_ne_zero.2 (Real.exp_pos _).ne'),
    integrable_exp_mul_expMeasure_iff]

/-- **The one sided hypotheses hold for the exponential feature law for every `0 < t < 2`**:
with `β* = 1 - 1/t`, `E[exp(|X - t| / 2)] < ∞` and, for `ε = (1 - 2β*) / 4 > 0`,
`E[exp(2 (1 + ε) β* (X - t))] < ∞`. -/
theorem oneSided_hypotheses_momentOrderExpLaw {t : ℝ} (ht0 : 0 < t) (ht2 : t < 2) :
    Integrable (fun y => Real.exp (1 / 2 * ‖y - featureLineVec t‖)) momentOrderExpLaw ∧
      ∃ ε, 0 < ε ∧ Integrable (fun y => Real.exp (2 * (1 + ε) *
        (featureLineVec (1 - 1 / t) ⬝ᵥ (y - featureLineVec t)))) momentOrderExpLaw := by
  refine ⟨(integrable_exp_momentOrderExpLaw_iff t (1 / 2)).2 (by norm_num), ?_⟩
  set b : ℝ := 1 - 1 / t with hb
  have hb2 : b < 1 / 2 := by
    have : (1 : ℝ) / 2 < 1 / t := (lt_one_div (by norm_num) ht0).2 (by linarith)
    linarith
  refine ⟨(1 - 2 * b) / 4, by linarith, ?_⟩
  rw [integrable_exp_directional_momentOrderExpLaw_iff]
  change 2 * (1 + (1 - 2 * b) / 4) * b < 1
  rcases le_or_gt b 0 with h | h
  · nlinarith
  · nlinarith

/-- **The exponential instance for every `0 < t < 2` under one sided moments.** The covariate
follows the standard exponential law, the assignment is a fair coin, `Y(true) = 1 + 2X`, and the
reported targets are `tₙ → t`. The weighted arm mean of arm `true` converges in probability to
`1 + 2t`. -/
theorem momentOrderInst_oneSided_consistent {t : ℝ} (ht0 : 0 < t) (ht2 : t < 2)
    {tn : ℕ → Fin 1 → ℝ} (htn : Tendsto tn atTop (𝓝 (featureLineVec t))) :
    IsConsistent (fun n ω => sampleBalancedArmMean id (tn n)
      (sharpInstSample momentOrderExpLaw sharpInstOutcome) true n ω) (1 + 2 * t)
      (sharpInstLaw momentOrderExpLaw sharpInstOutcome) := by
  obtain ⟨hexp, ε, hε, hdir⟩ := oneSided_hypotheses_momentOrderExpLaw ht0 ht2
  have h := momentOrderInst_consistent_of_isMinOn_oneSided measurable_sharpInstOutcome
    (mem_interior_momentOrderExpLaw ht0) (isMinOn_sharpDualObjective_momentOrderExpLaw ht0)
    (by norm_num) hexp hε hdir htn true sharpInstOutcome_true
  have hv : 1 + featureLineVec 2 ⬝ᵥ featureLineVec t = 1 + 2 * t := by
    simp [featureLineVec, dotProduct]
  rw [hv] at h
  exact h

/-- **At `t = 1/3` the theorem under a directional moment does not apply to the exponential
law**: with `β* = 1 - 3 = -2`, no order `κ > |β*|` has `E[exp(κ |X - 1/3|)] < ∞`. -/
theorem not_exists_order_directional_momentOrderExpLaw_one_third :
    ¬ ∃ κ : ℝ, Integrable (fun y => Real.exp (κ * ‖y - featureLineVec (1 / 3)‖))
        momentOrderExpLaw ∧ (1 : ℕ) * ‖featureLineVec (1 - 1 / (1 / 3 : ℝ))‖ < κ := by
  rintro ⟨κ, hi, hκ⟩
  rw [integrable_exp_momentOrderExpLaw_iff] at hi
  rw [norm_featureLineVec] at hκ
  norm_num at hκ
  linarith

/-- **The exponential instance at `t = 1/3`.** With `β* = -2` and the reported targets
`tₙ = 1/3 + 1/(n + 1) → 1/3`, the weighted arm mean of arm `true` converges in probability to
`1 + 2 · 1/3 = 5/3`. -/
theorem momentOrderInst_oneSided_one_third :
    IsConsistent (fun n ω => sampleBalancedArmMean id
      (featureLineVec (1 / 3 + 1 / ((n : ℝ) + 1)))
      (sharpInstSample momentOrderExpLaw sharpInstOutcome) true n ω) (5 / 3)
      (sharpInstLaw momentOrderExpLaw sharpInstOutcome) := by
  have htn : Tendsto (fun n : ℕ => featureLineVec (1 / 3 + 1 / ((n : ℝ) + 1))) atTop
      (𝓝 (featureLineVec (1 / 3))) := tendsto_pi_nhds.2 fun _ => by
    simpa [featureLineVec] using
      (tendsto_const_nhds (x := (1 / 3 : ℝ))).add
        (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  have h := momentOrderInst_oneSided_consistent (t := 1 / 3) (by norm_num) (by norm_num) htn
  rwa [show (1 : ℝ) + 2 * (1 / 3) = 5 / 3 by norm_num] at h

/-- **For `t ≥ 2` the directional moment fails for the exponential law**: with
`β* = 1 - 1/t ≥ 1/2`, `E[exp(2 (1 + ε) β* (X - t))] = ∞` for every `ε > 0`. -/
theorem not_integrable_directional_momentOrderExpLaw {t : ℝ} (ht : 2 ≤ t) {ε : ℝ}
    (hε : 0 < ε) :
    ¬ Integrable (fun y => Real.exp (2 * (1 + ε) *
      (featureLineVec (1 - 1 / t) ⬝ᵥ (y - featureLineVec t)))) momentOrderExpLaw := by
  rw [integrable_exp_directional_momentOrderExpLaw_iff, not_lt]
  change 1 ≤ 2 * (1 + ε) * (1 - 1 / t)
  have h : 1 / t ≤ 1 / 2 := one_div_le_one_div_of_le two_pos ht
  nlinarith

/-- `exp(c (X - t))` is integrable under the standard exponential law for `c < 1`. -/
theorem integrable_exp_mul_sub_expMeasure {c : ℝ} (hc : c < 1) (t : ℝ) :
    Integrable (fun x => Real.exp (c * (x - t))) (expMeasure 1) := by
  refine ((integrable_exp_mul_expMeasure_iff (c := c)).2 hc).const_mul (Real.exp (-(c * t)))
    |>.congr (ae_of_all _ fun x => ?_)
  simp only
  rw [← Real.exp_add]; ring_nf

/-- **An instance of `exists_integrable_exp_mul_pm_of_oneSided`**: for the standard exponential
law at `t = 1/3` with `β* = -2`, the moment `E[exp(|X - 1/3| / 2)]` and the directional moment
`E[exp(2 (1 + 1) β* (X - 1/3))]` give some `r > 0` with
`E[exp((β* ∓ r)(X - 1/3))] < ∞`. -/
theorem exists_integrable_exp_mul_pm_expMeasure_one_third :
    ∃ r, 0 < r ∧ Integrable (fun x => Real.exp ((-2 - r) * (x - 1 / 3))) (expMeasure 1) ∧
      Integrable (fun x => Real.exp ((-2 + r) * (x - 1 / 3))) (expMeasure 1) := by
  have hn : ∀ x : ℝ, ‖featureLineVec x - featureLineVec (1 / 3)‖ = |x - 1 / 3| := fun x => by
    rw [show featureLineVec x - featureLineVec (1 / 3) = featureLineVec (x - 1 / 3) from
      funext fun _ => rfl, norm_featureLineVec]
  have hexp : Integrable (fun x : ℝ => Real.exp (1 / 2 * |x - 1 / 3|)) (expMeasure 1) := by
    have h := (integrable_exp_norm_expMeasure_iff (1 / 3) (1 / 2)).2 (by norm_num)
    simp only [hn] at h
    exact h
  have hdir : Integrable (fun x : ℝ => Real.exp (2 * (1 + 1) * (-2) * (x - 1 / 3)))
      (expMeasure 1) := integrable_exp_mul_sub_expMeasure (by norm_num) _
  exact exists_integrable_exp_mul_pm_of_oneSided (g := fun x : ℝ => x - 1 / 3)
    (measurable_id.sub_const _) (by norm_num) hexp one_pos hdir

/-- **An instance of `integrable_exp_abs_of_integrable_exp_mul_pm`**: for the standard
exponential law at `t = 3/2` with `β* = 1/3` and `r = 1/2`, the finite moments
`E[exp(-(X - 3/2) / 6)]` and `E[exp(5 (X - 3/2) / 6)]` give `E[exp(|X - 3/2| / 6)] < ∞`. -/
theorem integrable_exp_abs_expMeasure_three_halves :
    Integrable (fun x : ℝ => Real.exp (1 / 6 * |x - 3 / 2|)) (expMeasure 1) := by
  have h := (integrable_exp_abs_of_integrable_exp_mul_pm (g := fun x : ℝ => x - 3 / 2)
    (β := 1 / 3) (r := 1 / 2) (measurable_id.sub_const _) (by norm_num) (by norm_num)
    (integrable_exp_mul_sub_expMeasure (by norm_num) _)
    (integrable_exp_mul_sub_expMeasure (by norm_num) _)).2
  rwa [show min ((1 : ℝ) / 2 - 1 / 3) (1 / 3 + 1 / 2) = 1 / 6 by norm_num] at h

end Exponential

end PopulationAdjustment

end CausalInference
