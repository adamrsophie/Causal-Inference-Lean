/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.MetaAnalysis.CochranQLaw
public import CausalInference.MetaAnalysis.RandomEffects

/-!
# Meta-analysis: the Hartung-Knapp interval

For weights `wᵢ = 1 / vᵢ` and `k` studies, the **Hartung-Knapp variance estimate** of the pooled
estimate is `V̂ = Q / ((k - 1) ∑ wᵢ) = ∑ wᵢ (yᵢ - θ̂)² / ((k - 1) ∑ wᵢ)` (`hartungKnappVariance`)
and the **Hartung-Knapp statistic** is `T = (θ̂ - θ) / √V̂` (`hartungKnappStat`).

**Exact `t` law.** If the estimates are independent with `Yᵢ ~ N(θ, σ² vᵢ)`, known `vᵢ > 0` and
an unknown scale `σ² > 0`, and `k = m + 1` with `m ≥ 1`, then `T ~ tₘ`
(`hasLaw_hartungKnappStat`). Proof: by the joint law of the pooled estimate and `Q`
(`hasLaw_ivwEstimate_cochranQ`), `(θ̂ - θ) / √(σ² / ∑ wᵢ) ~ N(0, 1)` and `Q / σ² ~ χ²ₘ` are
independent, and `T` is the first divided by the square root of the second over `m`; the scale
`σ²` cancels.

**Exact coverage.** Under the same hypotheses `V̂ > 0` almost surely (`Q / σ² ~ χ²ₘ` has no atom
at `0` for `m ≥ 1`), and for every `c` the interval `θ̂ ± c √V̂` covers `θ` with probability
exactly `tₘ([-c, c])` (`measure_hartungKnapp_coverage`).

**The random effects model.** In the Gaussian random effects model with known `τ²` the
estimates are independent with `Yᵢ ~ N(θ, vᵢ + τ²)`; with the random effects weights
`1 / (vᵢ + τ²)` the statistic has the exact `t_{k-1}` law and the interval has exact coverage
(`IsGaussianRandomEffectsModel.hasLaw_hartungKnappStat`,
`IsGaussianRandomEffectsModel.measure_hartungKnapp_coverage`).

The degrees of freedom `m = k - 1` must be at least `1`: for one study `Q = 0`, `V̂ = 0`, and
the statistic would be a division by zero.

## Main definitions

* `hartungKnappVariance`, `hartungKnappStat`.

## Main results

* `chiSquared_singleton_zero`, `hartungKnappStat_eq`.
* `hasLaw_hartungKnappStat`, `measure_hartungKnappVariance_eq_zero`,
  `measure_hartungKnapp_coverage`.
* `IsGaussianRandomEffectsModel.hasLaw_hartungKnappStat`,
  `IsGaussianRandomEffectsModel.measure_hartungKnapp_coverage`.

## References

* J. Hartung and G. Knapp, *A refined method for the meta-analysis of controlled clinical trials
  with binary outcome*, Statistics in Medicine 20 (2001).
-/

@[expose] public section

namespace CausalInference

namespace MetaAnalysis

open MeasureTheory ProbabilityTheory Finset
open scoped NNReal

section Definitions

variable {ι : Type*} [Fintype ι]

/-- The **Hartung-Knapp variance estimate** `V̂ = Q / ((k - 1) ∑ wᵢ)`, `wᵢ = 1 / vᵢ`. -/
noncomputable def hartungKnappVariance (v y : ι → ℝ) : ℝ :=
  cochranQ v y / (((Fintype.card ι : ℝ) - 1) * ∑ i, ivWeight v i)

/-- The **Hartung-Knapp statistic** `T = (θ̂ - θ) / √V̂` (Hartung and Knapp 2001). -/
noncomputable def hartungKnappStat (v : ι → ℝ) (θ : ℝ) (y : ι → ℝ) : ℝ :=
  (ivwEstimate v y - θ) / √(hartungKnappVariance v y)

@[fun_prop]
theorem measurable_hartungKnappVariance (v : ι → ℝ) :
    Measurable fun y : ι → ℝ => hartungKnappVariance v y := by
  unfold hartungKnappVariance
  fun_prop

@[fun_prop]
theorem measurable_hartungKnappStat (v : ι → ℝ) (θ : ℝ) :
    Measurable fun y : ι → ℝ => hartungKnappStat v θ y := by
  unfold hartungKnappStat
  fun_prop

/-- **The statistic as a `t` ratio**: for `k = m + 1`, positive variances and `σ² > 0`,
`T = ((θ̂ - θ) / √(σ² / ∑ wᵢ)) / √((Q / σ²) / m)`. -/
theorem hartungKnappStat_eq {v : ι → ℝ} (hv : ∀ i, 0 < v i) {m : ℕ}
    (hcard : Fintype.card ι = m + 1) {σ2 : ℝ} (hσ : 0 < σ2) (θ : ℝ) (y : ι → ℝ) :
    hartungKnappStat v θ y = ((ivwEstimate v y - θ) / √(σ2 / ∑ i, ivWeight v i)) /
      √(cochranQ v y / σ2 / m) := by
  have : Nonempty ι := Fintype.card_pos_iff.1 (by omega)
  have hW := sum_ivWeight_pos hv
  have hk : ((Fintype.card ι : ℝ) - 1) = m := by rw [hcard]; push_cast; ring
  rw [hartungKnappStat, hartungKnappVariance, hk, div_div, ← Real.sqrt_mul (div_pos hσ hW).le]
  congr 2
  field_simp

end Definitions

/-! ### The exact `t` law and the exact coverage -/

/-- `χ²ₘ` has no atom at `0` for `m ≥ 1`: `X₁² + ⋯ + Xₘ² = 0` forces `X₁ = 0`. -/
theorem chiSquared_singleton_zero {m : ℕ} (hm : 1 ≤ m) : chiSquared m {0} = 0 := by
  have hsub : (fun x : Fin m → ℝ => ∑ j, x j ^ 2) ⁻¹' {0} ⊆
      (Function.eval (⟨0, hm⟩ : Fin m)) ⁻¹' {0} := by
    intro x hx
    have hx' : ∑ j, x j ^ 2 = 0 := hx
    have := (Finset.sum_eq_zero_iff_of_nonneg fun j _ => sq_nonneg (x j)).1 hx'
      ⟨0, hm⟩ (Finset.mem_univ _)
    exact pow_eq_zero_iff two_ne_zero |>.1 this
  rw [chiSquared_eq_map_pi, Measure.map_apply (by fun_prop) (measurableSet_singleton 0)]
  refine measure_mono_null hsub ?_
  rw [(measurePreserving_eval (fun _ : Fin m => gaussianReal 0 1) _).measure_preimage
    (measurableSet_singleton 0).nullMeasurableSet]
  have := nullSingletonClass_gaussianReal (μ := 0) (v := 1) one_ne_zero
  exact measure_singleton 0

section Law

variable {ι Ω : Type*} [Fintype ι] {mΩ : MeasurableSpace Ω} {P : Measure Ω} {Y : ι → Ω → ℝ}
  {v : ι → ℝ} {θ : ℝ}

/-- **The Hartung-Knapp statistic has an exact `t` law** (Hartung and Knapp 2001). Let the
estimates be independent with `Yᵢ ~ N(θ, σ² vᵢ)`, `vᵢ > 0`, `σ² > 0`, from `k = m + 1` studies,
`m ≥ 1`. Then `T = (θ̂ - θ) / √V̂ ~ tₘ`, whatever the scale `σ²`. -/
theorem hasLaw_hartungKnappStat {m : ℕ} (hcard : Fintype.card ι = m + 1) (hm : 1 ≤ m)
    (hv : ∀ i, 0 < v i) {σ2 : ℝ} (hσ : 0 < σ2) (hind : iIndepFun Y P)
    (hY : ∀ i, HasLaw (Y i) (gaussianReal θ (σ2 * v i).toNNReal) P) :
    HasLaw (fun ω => hartungKnappStat v θ fun i => Y i ω) (studentT m) P := by
  have : Nonempty ι := Fintype.card_pos_iff.1 (by omega)
  have hW := sum_ivWeight_pos hv
  set s := √(σ2 / ∑ i, ivWeight v i) with hs
  have hs0 : 0 < s := Real.sqrt_pos.2 (div_pos hσ hW)
  have hjoint := hasLaw_ivwEstimate_cochranQ hcard hv hσ hind hY
  set g : ℝ × ℝ → ℝ × ℝ := fun p => ((p.1 - θ) / s, p.2) with hg
  have hstd : (gaussianReal θ (σ2 / ∑ i, ivWeight v i).toNNReal).map (fun a => (a - θ) / s) =
      gaussianReal 0 1 := by
    have hcomp : (fun a : ℝ => (a - θ) / s) = (fun a => a / s) ∘ fun a => a - θ := rfl
    rw [hcomp, ← Measure.map_map (by fun_prop) (by fun_prop), gaussianReal_map_sub_const,
      gaussianReal_map_div_const, sub_self, zero_div]
    congr 1
    ext
    simp only [NNReal.coe_div, NNReal.coe_mk, NNReal.coe_one, hs,
      Real.sq_sqrt (div_pos hσ hW).le, Real.coe_toNNReal _ (div_pos hσ hW).le]
    exact div_self (div_pos hσ hW).ne'
  have hG : HasLaw g ((gaussianReal 0 1).prod (chiSquared m))
      ((gaussianReal θ (σ2 / ∑ i, ivWeight v i).toNNReal).prod (chiSquared m)) := by
    refine ⟨by fun_prop, ?_⟩
    have : g = Prod.map (fun a => (a - θ) / s) id := rfl
    rw [this, ← Measure.map_prod_map _ _ (by fun_prop) measurable_id, hstd, Measure.map_id]
  have hT : HasLaw (fun p : ℝ × ℝ => p.1 / √(p.2 / m)) (studentT m)
      ((gaussianReal 0 1).prod (chiSquared m)) := ⟨by fun_prop, rfl⟩
  have hkey : (fun ω => hartungKnappStat v θ fun i => Y i ω) =
      (fun p : ℝ × ℝ => p.1 / √(p.2 / m)) ∘ g ∘
        fun ω => (ivwEstimate v (fun i => Y i ω), cochranQ v (fun i => Y i ω) / σ2) := by
    funext ω
    simp only [Function.comp_apply, hg]
    rw [hartungKnappStat_eq hv hcard hσ]
  rw [hkey]
  exact hT.comp (hG.comp hjoint)

/-- **The Hartung-Knapp variance estimate is positive almost surely**: under the hypotheses of
`hasLaw_hartungKnappStat`, `P(V̂ = 0) = 0`. -/
theorem measure_hartungKnappVariance_eq_zero {m : ℕ} (hcard : Fintype.card ι = m + 1)
    (hm : 1 ≤ m) (hv : ∀ i, 0 < v i) {σ2 : ℝ} (hσ : 0 < σ2) (hind : iIndepFun Y P)
    (hY : ∀ i, HasLaw (Y i) (gaussianReal θ (σ2 * v i).toNNReal) P) :
    P {ω | hartungKnappVariance v (fun i => Y i ω) = 0} = 0 := by
  have : Nonempty ι := Fintype.card_pos_iff.1 (by omega)
  have hW := sum_ivWeight_pos hv
  have hden : 0 < ((Fintype.card ι : ℝ) - 1) * ∑ i, ivWeight v i := by
    refine mul_pos ?_ hW
    rw [hcard]; push_cast
    have : (1 : ℝ) ≤ m := by exact_mod_cast hm
    linarith
  have hQ := hasLaw_cochranQ_div hcard hv hσ hind hY
  have hset : {ω | hartungKnappVariance v (fun i => Y i ω) = 0} =
      (fun ω => cochranQ v (fun i => Y i ω) / σ2) ⁻¹' {0} := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_preimage, Set.mem_singleton_iff, hartungKnappVariance,
      div_eq_zero_iff, hden.ne', hσ.ne', or_false]
  rw [hset, ← Measure.map_apply_of_aemeasurable hQ.aemeasurable (measurableSet_singleton 0),
    hQ.map_eq]
  exact chiSquared_singleton_zero hm

/-- **The Hartung-Knapp interval has exact coverage** (Hartung and Knapp 2001). Under the
hypotheses of `hasLaw_hartungKnappStat`, for every `c` the interval `θ̂ ± c √V̂` covers `θ` with
probability exactly `tₘ([-c, c])`. Proof: off the null event `{V̂ = 0}` the coverage event is
`{|T| ≤ c}`. -/
theorem measure_hartungKnapp_coverage {m : ℕ} (hcard : Fintype.card ι = m + 1) (hm : 1 ≤ m)
    (hv : ∀ i, 0 < v i) {σ2 : ℝ} (hσ : 0 < σ2) (hind : iIndepFun Y P)
    (hY : ∀ i, HasLaw (Y i) (gaussianReal θ (σ2 * v i).toNNReal) P) (c : ℝ) :
    P {ω | |ivwEstimate v (fun i => Y i ω) - θ| ≤
        c * √(hartungKnappVariance v fun i => Y i ω)} = studentT m (Set.Icc (-c) c) := by
  have hT := hasLaw_hartungKnappStat hcard hm hv hσ hind hY
  have hnull := measure_hartungKnappVariance_eq_zero hcard hm hv hσ hind hY
  have : Nonempty ι := Fintype.card_pos_iff.1 (by omega)
  have hW := sum_ivWeight_pos hv
  have hden : 0 ≤ ((Fintype.card ι : ℝ) - 1) * ∑ i, ivWeight v i := by
    refine mul_nonneg ?_ hW.le
    rw [hcard]; push_cast; linarith
  have hT' : P {ω | |hartungKnappStat v θ fun i => Y i ω| ≤ c} =
      studentT m (Set.Icc (-c) c) := by
    have hset : {ω | |hartungKnappStat v θ fun i => Y i ω| ≤ c} =
        (fun ω => hartungKnappStat v θ fun i => Y i ω) ⁻¹' Set.Icc (-c) c := by
      ext ω
      simp [abs_le]
    rw [hset, ← Measure.map_apply_of_aemeasurable hT.aemeasurable measurableSet_Icc, hT.map_eq]
  rw [← hT']
  refine measure_congr ?_
  have hae : ∀ᵐ ω ∂P, hartungKnappVariance v (fun i => Y i ω) ≠ 0 := by
    rw [ae_iff]
    simpa only [ne_eq, not_not] using hnull
  filter_upwards [hae] with ω hω
  have hV0 : 0 ≤ hartungKnappVariance v fun i => Y i ω :=
    div_nonneg (cochranQ_nonneg hv _) hden
  have hsq : 0 < √(hartungKnappVariance v fun i => Y i ω) :=
    Real.sqrt_pos.2 (lt_of_le_of_ne hV0 (Ne.symm hω))
  change |ivwEstimate v (fun i => Y i ω) - θ| ≤ c * √(hartungKnappVariance v fun i => Y i ω) ↔
    |hartungKnappStat v θ fun i => Y i ω| ≤ c
  rw [hartungKnappStat, abs_div, abs_of_pos hsq, div_le_iff₀ hsq]

end Law

/-! ### The random effects model with known `τ²` -/

namespace IsGaussianRandomEffectsModel

variable {ι Ω : Type*} [Fintype ι] {mΩ : MeasurableSpace Ω} {P : Measure Ω}
  {b ε : ι → Ω → ℝ} {τ2 : ℝ} {v : ι → ℝ}

variable (h : IsGaussianRandomEffectsModel P b ε τ2 v)
include h

/-- **The Hartung-Knapp statistic in the random effects model**: with known `τ²`, the random
effects weights `1 / (vᵢ + τ²)` and `k = m + 1 ≥ 2` studies, the statistic built from
`Yᵢ = θ + bᵢ + εᵢ` has the exact law `tₘ`. -/
theorem hasLaw_hartungKnappStat {m : ℕ} (hcard : Fintype.card ι = m + 1) (hm : 1 ≤ m)
    (θ : ℝ) :
    HasLaw (fun ω => hartungKnappStat (fun i => v i + τ2) θ fun i => θ + b i ω + ε i ω)
      (studentT m) P := by
  have hG := h.isGaussianCommonEffectModel θ
  exact MetaAnalysis.hasLaw_hartungKnappStat hcard hm hG.pos one_pos hG.indep
    fun i => by simpa only [one_mul] using hG.hasLaw i

/-- **Exact coverage of the Hartung-Knapp interval in the random effects model**: with known
`τ²` and `k = m + 1 ≥ 2` studies, the interval `θ̂ ± c √V̂` with the random effects weights covers
`θ` with probability exactly `tₘ([-c, c])`. -/
theorem measure_hartungKnapp_coverage {m : ℕ} (hcard : Fintype.card ι = m + 1) (hm : 1 ≤ m)
    (θ c : ℝ) :
    P {ω | |ivwEstimate (fun i => v i + τ2) (fun i => θ + b i ω + ε i ω) - θ| ≤
        c * √(hartungKnappVariance (fun i => v i + τ2) fun i => θ + b i ω + ε i ω)} =
      studentT m (Set.Icc (-c) c) := by
  have hG := h.isGaussianCommonEffectModel θ
  exact MetaAnalysis.measure_hartungKnapp_coverage hcard hm hG.pos one_pos hG.indep
    (fun i => by simpa only [one_mul] using hG.hasLaw i) c

end IsGaussianRandomEffectsModel

end MetaAnalysis

end CausalInference
