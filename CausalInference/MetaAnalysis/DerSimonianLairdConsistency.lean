/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.MetaAnalysis.DerSimonianLaird
public import CausalInference.MetaAnalysis.RestrictedLikelihoodMaximizer
public import CausalInference.Estimation.Consistency

/-!
# Meta-analysis: consistency of the DerSimonian-Laird estimator as the number of studies grows

A sequence of studies `Y₀, Y₁, …` is observed and the estimators are computed from the first `k`
studies, `k → ∞`. This file proves the consistency of the DerSimonian-Laird estimators when all
within study variances are equal, `vᵢ = v > 0`.

**The estimator under equal variances.** For `k ≥ 2` studies with the common variance `v`,
`Q = ∑ (yᵢ - ȳ)² / v` and `c = (k - 1) / v`, so the untruncated estimator is the sample variance
minus `v` (`dlTau2Untruncated_equalVar`):

`τ̂²_DL = ∑ (yᵢ - ȳ)² / (k - 1) - v`,

and the pooled estimate is the arithmetic mean `ȳ` for every value of `τ̂²_DL`, because the
weights `1 / (v + τ̂²_DL)` are equal (`dlEstimate_equalVar`).

**Consistency.** Let the estimates be i.i.d. with finite second moment, mean `θ` and variance
`v + τ²`, `v > 0`, `τ² ≥ 0`. By the strong law of large numbers for `Yᵢ` and `Yᵢ²`, almost
surely the untruncated and the truncated estimators converge to `τ²` and the pooled estimate to
`θ` (`tendsto_dl_equalVar_ae`); hence all three are consistent, in probability
(`isConsistent_dl_equalVar`). In the Gaussian random effects model `Yᵢ = θ + bᵢ + εᵢ`, with the
pairs `(bᵢ, εᵢ)` i.i.d. of law `N(0, τ²) ⊗ N(0, v)`, every hypothesis holds
(`isConsistent_dl_gaussianRandomEffects`).

The truncation `max 0 _` does not affect the limit, since `τ² ≥ 0` and `max 0` is continuous. The
case of unequal within study variances is not treated in this file.

## Main results

* `dlTau2Untruncated_equalVar`, `dlEstimate_equalVar`.
* `tendsto_dl_equalVar_ae`, `isConsistent_dl_equalVar`, `isConsistent_dl_gaussianRandomEffects`.

## References

* R. DerSimonian and N. Laird, *Meta-analysis in clinical trials*, Controlled Clinical Trials 7
  (1986).
-/

@[expose] public section

namespace CausalInference

namespace MetaAnalysis

open MeasureTheory ProbabilityTheory Filter Finset PopulationAdjustment
open scoped Topology

/-! ### The estimator under equal variances -/

section Deterministic

variable {ι : Type*} [Fintype ι]

/-- `∑ (yᵢ - ȳ)² = ∑ yᵢ² - k ȳ²`. -/
theorem regSxx_eq_sum_sq_sub [Nonempty ι] (y : ι → ℝ) :
    regSxx y = ∑ i, y i ^ 2 - Fintype.card ι * regMean y ^ 2 := by
  have hk : (Fintype.card ι : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hsum : ∑ i, y i = Fintype.card ι * regMean y := by
    rw [regMean]; field_simp
  have h : ∀ i, (y i - regMean y) ^ 2 = y i ^ 2 + (-2 * regMean y) * y i + regMean y ^ 2 :=
    fun i => by ring
  rw [regSxx, Finset.sum_congr rfl fun i _ => h i, Finset.sum_add_distrib,
    Finset.sum_add_distrib, ← Finset.mul_sum, hsum, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul]
  ring

/-- **The DerSimonian-Laird estimator under equal variances is the sample variance minus `v`**:
for `k ≥ 2` studies with the common variance `v > 0`, `τ̂²_DL = ∑ (yᵢ - ȳ)² / (k - 1) - v`. -/
theorem dlTau2Untruncated_equalVar (hk : 2 ≤ Fintype.card ι) {v : ℝ} (hv : 0 < v)
    (y : ι → ℝ) :
    dlTau2Untruncated (fun _ : ι => v) y = regSxx y / ((Fintype.card ι : ℝ) - 1) - v := by
  have hne : Nonempty ι := Fintype.card_pos_iff.1 (by omega)
  have hk' : (Fintype.card ι : ℝ) - 1 ≠ 0 := by
    have : (2 : ℝ) ≤ Fintype.card ι := by exact_mod_cast hk
    linarith
  have hkpos : (Fintype.card ι : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hQ : cochranQ (fun _ : ι => v) y = regSxx y / v := by
    rw [cochranQ, ivwEstimate_equalVar hv.ne', regSxx, Finset.sum_div]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [ivWeight]
    ring
  have hc : cochranQSlope (fun _ : ι => v) = ((Fintype.card ι : ℝ) - 1) / v := by
    simp only [cochranQSlope, ivWeight, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    field_simp
  rw [dlTau2Untruncated, hQ, hc]
  field_simp

/-- **The pooled estimate under equal variances is the arithmetic mean**, whatever the estimate
of the between study variance. -/
theorem dlEstimate_equalVar [Nonempty ι] {v : ℝ} (hv : 0 < v) (y : ι → ℝ) :
    dlEstimate (fun _ : ι => v) y = regMean y := by
  rw [dlEstimate]
  exact ivwEstimate_equalVar (by linarith [dlTau2_nonneg (fun _ : ι => v) y]) y

theorem measurable_dlEstimate (v : ι → ℝ) : Measurable fun y : ι → ℝ => dlEstimate v y := by
  have hd := measurable_dlTau2 v
  unfold dlEstimate ivwEstimate weightedMean ivWeight
  fun_prop

end Deterministic

/-! ### Consistency -/

section Consistency

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}

/-- The DerSimonian-Laird estimators from the first `k` studies, as a function of the sample. -/
theorem dl_firstK_eq {Y : ℕ → Ω → ℝ} {v : ℝ} (hv : 0 < v) {k : ℕ} (hk : 2 ≤ k) (ω : Ω) :
    dlTau2Untruncated (fun _ : Fin k => v) (fun i => Y i ω) =
        (k : ℝ) / (k - 1) *
          ((k : ℝ)⁻¹ * ∑ i ∈ range k, Y i ω ^ 2 - ((k : ℝ)⁻¹ * ∑ i ∈ range k, Y i ω) ^ 2) - v ∧
      dlEstimate (fun _ : Fin k => v) (fun i => Y i ω) = (k : ℝ)⁻¹ * ∑ i ∈ range k, Y i ω := by
  have hne : Nonempty (Fin k) := ⟨⟨0, by omega⟩⟩
  have hkpos : (k : ℝ) ≠ 0 := by exact_mod_cast (show k ≠ 0 by omega)
  have hk1 : (k : ℝ) - 1 ≠ 0 := by
    have : (2 : ℝ) ≤ k := by exact_mod_cast hk
    linarith
  have h1 : ∑ i : Fin k, Y i ω = ∑ i ∈ range k, Y i ω := Fin.sum_univ_eq_sum_range (Y · ω) k
  have h2 : ∑ i : Fin k, Y i ω ^ 2 = ∑ i ∈ range k, Y i ω ^ 2 :=
    Fin.sum_univ_eq_sum_range (fun i => Y i ω ^ 2) k
  have hmean : regMean (fun i : Fin k => Y i ω) = (k : ℝ)⁻¹ * ∑ i ∈ range k, Y i ω := by
    rw [regMean, h1, Fintype.card_fin]
    field_simp
  refine ⟨?_, by rw [dlEstimate_equalVar hv, hmean]⟩
  rw [dlTau2Untruncated_equalVar (by simpa using hk) hv, regSxx_eq_sum_sq_sub, hmean, h2,
    Fintype.card_fin]
  field_simp

/-- **Strong consistency of the DerSimonian-Laird estimators under equal variances.** Let the
estimates be i.i.d. with finite second moment, mean `θ` and variance `v + τ²`, `v > 0`, `τ² ≥ 0`.
Then almost surely, computed from the first `k` studies with the common within study variance
`v`, the untruncated and the truncated DerSimonian-Laird estimators converge to `τ²` and the
pooled estimate converges to `θ` as `k → ∞`. -/
theorem tendsto_dl_equalVar_ae [IsProbabilityMeasure P] {Y : ℕ → Ω → ℝ} (hY : IsIIDSample Y P)
    (hmem : MemLp (Y 0) 2 P)
    {θ v τ2 : ℝ} (hθ : P[Y 0] = θ) (hvar : Var[Y 0; P] = v + τ2) (hv : 0 < v) (hτ : 0 ≤ τ2) :
    ∀ᵐ ω ∂P,
      Tendsto (fun k => dlTau2Untruncated (fun _ : Fin k => v) fun i => Y i ω) atTop (𝓝 τ2) ∧
      Tendsto (fun k => dlTau2 (fun _ : Fin k => v) fun i => Y i ω) atTop (𝓝 τ2) ∧
      Tendsto (fun k => dlEstimate (fun _ : Fin k => v) fun i => Y i ω) atTop (𝓝 θ) := by
  have hY1 : IsIIDSample (fun i ω => id (Y i ω)) P := hY.comp measurable_id
  have hY2 : IsIIDSample (fun i ω => Y i ω ^ 2) P := hY.comp (measurable_id.pow_const 2)
  have hs1 := strong_law_ae_real (fun i ω => Y i ω) (hmem.integrable one_le_two)
    (fun i j hij => hY1.indep.indepFun hij) hY1.ident
  have hs2 := strong_law_ae_real (fun i ω => Y i ω ^ 2) hmem.integrable_sq
    (fun i j hij => hY2.indep.indepFun hij) hY2.ident
  have hm2 : P[fun ω => Y 0 ω ^ 2] = v + τ2 + θ ^ 2 := by
    have h := variance_eq_sub hmem
    have hX : (Y 0) ^ 2 = fun ω => Y 0 ω ^ 2 := by
      funext ω; simp only [Pi.pow_apply]
    rw [hX, hθ, hvar] at h
    linarith
  have hfrac : Tendsto (fun k : ℕ => (k : ℝ) / (k - 1)) atTop (𝓝 1) := by
    simpa only [← sub_eq_add_neg] using tendsto_natCast_div_add_atTop (-1 : ℝ)
  filter_upwards [hs1, hs2] with ω h1 h2
  have h1' : Tendsto (fun k : ℕ => (k : ℝ)⁻¹ * ∑ i ∈ range k, Y i ω) atTop (𝓝 θ) := by
    rw [← hθ]; simpa [div_eq_inv_mul] using h1
  have h2' : Tendsto (fun k : ℕ => (k : ℝ)⁻¹ * ∑ i ∈ range k, Y i ω ^ 2) atTop
      (𝓝 (v + τ2 + θ ^ 2)) := by
    rw [← hm2]; simpa [div_eq_inv_mul] using h2
  have hlim : Tendsto (fun k : ℕ => (k : ℝ) / (k - 1) *
      ((k : ℝ)⁻¹ * ∑ i ∈ range k, Y i ω ^ 2 - ((k : ℝ)⁻¹ * ∑ i ∈ range k, Y i ω) ^ 2) - v)
      atTop (𝓝 (1 * (v + τ2 + θ ^ 2 - θ ^ 2) - v)) :=
    ((hfrac.mul (h2'.sub (h1'.pow 2))).sub tendsto_const_nhds)
  have hval : 1 * (v + τ2 + θ ^ 2 - θ ^ 2) - v = τ2 := by ring
  rw [hval] at hlim
  have hraw : Tendsto (fun k => dlTau2Untruncated (fun _ : Fin k => v) fun i => Y i ω) atTop
      (𝓝 τ2) := by
    refine hlim.congr' ?_
    filter_upwards [eventually_ge_atTop 2] with k hk
    exact (dl_firstK_eq hv hk ω).1.symm
  refine ⟨hraw, ?_, ?_⟩
  · have := ((continuous_const (y := (0 : ℝ)) |>.max continuous_id).tendsto τ2).comp hraw
    simpa [Function.comp_def, dlTau2, max_eq_right hτ] using this
  · refine h1'.congr' ?_
    filter_upwards [eventually_ge_atTop 2] with k hk
    exact (dl_firstK_eq hv hk ω).2.symm

/-- **Consistency of the DerSimonian-Laird estimators under equal variances**: under the
hypotheses of `tendsto_dl_equalVar_ae`, the untruncated and the truncated estimators are
consistent for `τ²` and the pooled estimate is consistent for `θ`. -/
theorem isConsistent_dl_equalVar [IsProbabilityMeasure P] {Y : ℕ → Ω → ℝ}
    (hY : IsIIDSample Y P) (hmem : MemLp (Y 0) 2 P) {θ v τ2 : ℝ} (hθ : P[Y 0] = θ)
    (hvar : Var[Y 0; P] = v + τ2) (hv : 0 < v) (hτ : 0 ≤ τ2) :
    IsConsistent (fun k ω => dlTau2Untruncated (fun _ : Fin k => v) fun i => Y i ω) τ2 P ∧
      IsConsistent (fun k ω => dlTau2 (fun _ : Fin k => v) fun i => Y i ω) τ2 P ∧
      IsConsistent (fun k ω => dlEstimate (fun _ : Fin k => v) fun i => Y i ω) θ P := by
  have hae := tendsto_dl_equalVar_ae hY hmem hθ hvar hv hτ
  have hYm : ∀ k : ℕ, AEMeasurable (fun ω => fun i : Fin k => Y i ω) P := fun k =>
    AEMeasurable.of_eval fun i => hY.aemeasurable i
  refine ⟨tendstoInMeasure_of_tendsto_ae (fun k => ?_) (hae.mono fun ω h => h.1),
    tendstoInMeasure_of_tendsto_ae (fun k => ?_) (hae.mono fun ω h => h.2.1),
    tendstoInMeasure_of_tendsto_ae (fun k => ?_) (hae.mono fun ω h => h.2.2)⟩
  · exact ((measurable_dlTau2Untruncated _).comp_aemeasurable (hYm k)).aestronglyMeasurable
  · exact ((measurable_dlTau2 _).comp_aemeasurable (hYm k)).aestronglyMeasurable
  · exact ((measurable_dlEstimate _).comp_aemeasurable (hYm k)).aestronglyMeasurable

/-- **Consistency in the Gaussian random effects model with equal variances**: let the pairs
`(bᵢ, εᵢ)` of study effects and errors be i.i.d. with the law `N(0, τ²) ⊗ N(0, v)`, `v > 0`,
`τ² ≥ 0`, and `Yᵢ = θ + bᵢ + εᵢ`. Then from the first `k` studies the untruncated and the
truncated DerSimonian-Laird estimators are consistent for `τ²` and the pooled estimate is
consistent for `θ`. -/
theorem isConsistent_dl_gaussianRandomEffects [IsProbabilityMeasure P] {b ε : ℕ → Ω → ℝ}
    (hZ : IsIIDSample (fun i ω => (b i ω, ε i ω)) P) {v τ2 : ℝ} (hv : 0 < v) (hτ : 0 ≤ τ2)
    (hlaw : HasLaw (fun ω => (b 0 ω, ε 0 ω))
      ((gaussianReal 0 τ2.toNNReal).prod (gaussianReal 0 v.toNNReal)) P) (θ : ℝ) :
    IsConsistent (fun k ω => dlTau2Untruncated (fun _ : Fin k => v)
        fun i => θ + b i ω + ε i ω) τ2 P ∧
      IsConsistent (fun k ω => dlTau2 (fun _ : Fin k => v) fun i => θ + b i ω + ε i ω) τ2 P ∧
      IsConsistent (fun k ω => dlEstimate (fun _ : Fin k => v)
        fun i => θ + b i ω + ε i ω) θ P := by
  have hY : IsIIDSample (fun i ω => θ + b i ω + ε i ω) P :=
    hZ.comp (f := fun p : ℝ × ℝ => θ + p.1 + p.2) (by fun_prop)
  have hF : HasLaw (fun p : ℝ × ℝ => θ + p.1 + p.2) (gaussianReal θ (v + τ2).toNNReal)
      ((gaussianReal 0 τ2.toNNReal).prod (gaussianReal 0 v.toNNReal)) := by
    refine ⟨by fun_prop, ?_⟩
    have hsplit : (fun p : ℝ × ℝ => θ + p.1 + p.2) =
        (fun x => θ + x) ∘ fun p : ℝ × ℝ => p.1 + p.2 := by
      funext p
      simp only [Function.comp_apply]
      ring
    rw [hsplit, ← Measure.map_map (by fun_prop) (by fun_prop)]
    change ((gaussianReal 0 τ2.toNNReal) ∗ (gaussianReal 0 v.toNNReal)).map _ = _
    rw [gaussianReal_conv_gaussianReal, gaussianReal_map_const_add, add_zero, zero_add,
      add_comm v, Real.toNNReal_add hτ hv.le]
  have h0 : HasLaw (fun ω => θ + b 0 ω + ε 0 ω) (gaussianReal θ (v + τ2).toNNReal) P :=
    hF.comp hlaw
  have hvτ : 0 ≤ v + τ2 := by linarith
  refine isConsistent_dl_equalVar hY (h0.memLp (memLp_id_gaussianReal 2)) ?_ ?_ hv hτ
  · rw [h0.integral_eq, integral_id_gaussianReal]
  · rw [h0.variance_eq, variance_id_gaussianReal, Real.coe_toNNReal _ hvτ]

end Consistency

end MetaAnalysis

end CausalInference
