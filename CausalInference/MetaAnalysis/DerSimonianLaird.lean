/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.MetaAnalysis.RandomEffects

/-!
# Meta-analysis: the DerSimonian-Laird estimator of the between study variance

In the random effects model `Yᵢ = θ + bᵢ + εᵢ` with between study variance `τ²`, Cochran's `Q`
with the within-study weights `wᵢ = 1 / vᵢ` has expectation `E[Q] = (k - 1) + τ² c`, with the
slope `c = ∑ wᵢ - ∑ wᵢ² / ∑ wᵢ > 0` for `k ≥ 2` studies (`IsRandomEffectsModel.integral_cochranQ`,
`cochranQSlope_pos`). Solving the moment equation for `τ²` gives the **untruncated** moment
estimator `(Q - (k - 1)) / c` (`dlTau2Untruncated`); since a variance is not negative, the
**DerSimonian-Laird estimator** truncates it at zero, `τ̂²_DL = max 0 ((Q - (k - 1)) / c)`
(`dlTau2`). The random effects pooled estimate with the estimated weights `1 / (vᵢ + τ̂²_DL)` is
`dlEstimate`.

* **Unbiasedness of the untruncated estimator**: in the moment form of the model, with `k ≥ 2`,
  `(Q - (k - 1)) / c` is integrable and `E[(Q - (k - 1)) / c] = τ²`
  (`IsRandomEffectsModel.integral_dlTau2Untruncated`).
* **Upward bias of the truncated estimator**: `τ̂²_DL` is integrable and `E[τ̂²_DL] ≥ τ²`
  (`IsRandomEffectsModel.le_integral_dlTau2`). In the Gaussian model the inequality is strict
  for every `τ² ≥ 0` (`IsGaussianRandomEffectsModel.lt_integral_dlTau2`): the event
  `{Q < k - 1}`, on which the truncation is active, has positive probability
  (`IsGaussianRandomEffectsModel.measure_cochranQ_lt_pos`), because it is an open set of data
  vectors that contains the constant vectors and the law `⊗ᵢ N(θ, vᵢ + τ²)` charges every
  nonempty open set.

The estimator needs `k ≥ 2`: with one study `Q = 0` and `c = 0` (`cochranQ_of_card_eq_one`,
`cochranQSlope_of_card_eq_one`), and `(Q - (k - 1)) / c` would be a division by zero.

## Main definitions

* `dlTau2Untruncated`, `dlTau2`, `dlEstimate`.

## Main results

* `dlTau2_nonneg`, `dlTau2_eq_zero_iff`, `dlTau2_eq_untruncated_iff`,
  `dlTau2Untruncated_le_dlTau2`, `continuous_dlTau2Untruncated`.
* `IsRandomEffectsModel.integral_dlTau2Untruncated`, `IsRandomEffectsModel.le_integral_dlTau2`.
* `IsGaussianRandomEffectsModel.measure_cochranQ_lt_pos`,
  `IsGaussianRandomEffectsModel.lt_integral_dlTau2`.

## References

* R. DerSimonian and N. Laird, *Meta-analysis in clinical trials*, Controlled Clinical Trials 7
  (1986).
-/

@[expose] public section

namespace CausalInference

namespace MetaAnalysis

open MeasureTheory ProbabilityTheory Finset PopulationAdjustment

section Estimator

variable {ι : Type*} [Fintype ι] {v : ι → ℝ}

/-- The **untruncated moment estimator** of `τ²`: `(Q - (k - 1)) / c`, with `Q` and the slope
`c = cochranQSlope v` computed from the within-study variances `vᵢ`. -/
noncomputable def dlTau2Untruncated (v y : ι → ℝ) : ℝ :=
  (cochranQ v y - ((Fintype.card ι : ℝ) - 1)) / cochranQSlope v

/-- The **DerSimonian-Laird estimator** of the between study variance, truncated at zero:
`τ̂²_DL = max 0 ((Q - (k - 1)) / c)` (DerSimonian and Laird 1986). -/
noncomputable def dlTau2 (v y : ι → ℝ) : ℝ :=
  max 0 (dlTau2Untruncated v y)

/-- The **DerSimonian-Laird random effects pooled estimate**: the inverse variance weighted mean
with the estimated weights `1 / (vᵢ + τ̂²_DL)`. -/
noncomputable def dlEstimate (v y : ι → ℝ) : ℝ :=
  ivwEstimate (fun i => v i + dlTau2 v y) y

theorem dlTau2_nonneg (v y : ι → ℝ) : 0 ≤ dlTau2 v y := le_max_left _ _

theorem dlTau2Untruncated_le_dlTau2 (v y : ι → ℝ) : dlTau2Untruncated v y ≤ dlTau2 v y :=
  le_max_right _ _

/-- **The truncation is active exactly when `Q ≤ k - 1`**: `τ̂²_DL = 0 ↔ Q ≤ k - 1` (two or more
studies). -/
theorem dlTau2_eq_zero_iff (hv : ∀ i, 0 < v i) (hk : 2 ≤ Fintype.card ι) (y : ι → ℝ) :
    dlTau2 v y = 0 ↔ cochranQ v y ≤ (Fintype.card ι : ℝ) - 1 := by
  have hc := cochranQSlope_pos hv (by omega)
  rw [dlTau2, max_eq_left_iff, dlTau2Untruncated, div_nonpos_iff]
  constructor
  · rintro (⟨-, h⟩ | ⟨h, -⟩)
    · exact absurd h (not_le.2 hc)
    · linarith
  · intro h
    exact Or.inr ⟨by linarith, hc.le⟩

/-- `τ̂²_DL` equals the untruncated estimator exactly when `Q ≥ k - 1` (two or more studies). -/
theorem dlTau2_eq_untruncated_iff (hv : ∀ i, 0 < v i) (hk : 2 ≤ Fintype.card ι) (y : ι → ℝ) :
    dlTau2 v y = dlTau2Untruncated v y ↔ (Fintype.card ι : ℝ) - 1 ≤ cochranQ v y := by
  have hc := cochranQSlope_pos hv (by omega)
  rw [dlTau2, max_eq_right_iff, dlTau2Untruncated, le_div_iff₀ hc, zero_mul, sub_nonneg]

/-- `Q` is a continuous function of the data vector. -/
theorem continuous_cochranQ (v : ι → ℝ) : Continuous fun y : ι → ℝ => cochranQ v y := by
  unfold cochranQ ivwEstimate weightedMean
  fun_prop

theorem continuous_dlTau2Untruncated (v : ι → ℝ) :
    Continuous fun y : ι → ℝ => dlTau2Untruncated v y := by
  unfold dlTau2Untruncated
  exact ((continuous_cochranQ v).sub continuous_const).div_const _

@[fun_prop]
theorem measurable_dlTau2Untruncated (v : ι → ℝ) :
    Measurable fun y : ι → ℝ => dlTau2Untruncated v y :=
  (continuous_dlTau2Untruncated v).measurable

@[fun_prop]
theorem measurable_dlTau2 (v : ι → ℝ) : Measurable fun y : ι → ℝ => dlTau2 v y :=
  measurable_const.max (measurable_dlTau2Untruncated v)

end Estimator

/-! ### Bias in the moment model -/

namespace IsRandomEffectsModel

variable {ι Ω : Type*} [Fintype ι] {mΩ : MeasurableSpace Ω} {P : Measure Ω}
  {b ε : ι → Ω → ℝ} {τ2 : ℝ} {v : ι → ℝ}

variable (h : IsRandomEffectsModel P b ε τ2 v)
include h

/-- **The untruncated moment estimator is unbiased** (DerSimonian and Laird 1986): in the
random effects model with `k ≥ 2` studies, `(Q - (k - 1)) / c` is integrable and
`E[(Q - (k - 1)) / c] = τ²`. Proof: `E[Q] = (k - 1) + τ² c` with `c > 0`. -/
theorem integral_dlTau2Untruncated (hk : 2 ≤ Fintype.card ι) (θ : ℝ) :
    Integrable (fun ω => dlTau2Untruncated v fun i => θ + b i ω + ε i ω) P ∧
      ∫ ω, dlTau2Untruncated v (fun i => θ + b i ω + ε i ω) ∂P = τ2 := by
  have := h.isProbabilityMeasure
  have : Nonempty ι := Fintype.card_pos_iff.1 (by omega)
  obtain ⟨hint, hE⟩ := h.integral_cochranQ θ
  have hc := cochranQSlope_pos h.pos (by omega)
  refine ⟨(hint.sub (integrable_const _)).div_const _, ?_⟩
  simp only [dlTau2Untruncated]
  rw [integral_div, integral_sub hint (integrable_const _), hE, integral_const, smul_eq_mul,
    probReal_univ, one_mul]
  field_simp
  ring

/-- **The truncated estimator is biased upward**: in the random effects model with `k ≥ 2`
studies, `τ̂²_DL` is integrable and `τ² ≤ E[τ̂²_DL]`. -/
theorem le_integral_dlTau2 (hk : 2 ≤ Fintype.card ι) (θ : ℝ) :
    Integrable (fun ω => dlTau2 v fun i => θ + b i ω + ε i ω) P ∧
      τ2 ≤ ∫ ω, dlTau2 v (fun i => θ + b i ω + ε i ω) ∂P := by
  have := h.isProbabilityMeasure
  obtain ⟨hint, hE⟩ := h.integral_dlTau2Untruncated hk θ
  have hint' : Integrable (fun ω => dlTau2 v fun i => θ + b i ω + ε i ω) P :=
    (integrable_const 0).sup hint
  refine ⟨hint', ?_⟩
  rw [← hE]
  exact integral_mono hint hint' fun ω => dlTau2Untruncated_le_dlTau2 v _

end IsRandomEffectsModel

/-! ### Strict bias in the Gaussian model -/

namespace IsGaussianRandomEffectsModel

variable {ι Ω : Type*} [Fintype ι] {mΩ : MeasurableSpace Ω} {P : Measure Ω}
  {b ε : ι → Ω → ℝ} {τ2 : ℝ} {v : ι → ℝ}

variable (h : IsGaussianRandomEffectsModel P b ε τ2 v)
include h

/-- **The truncation is active with positive probability**: in the Gaussian random effects
model with `k ≥ 2` studies, `P(Q < k - 1) > 0`, equivalently `P((Q - (k - 1)) / c < 0) > 0`.
Proof: the set of data vectors with `Q < k - 1` is open and contains the constant vectors (where
`Q = 0`), and `⊗ᵢ N(θ, vᵢ + τ²)` charges every nonempty open set. -/
theorem measure_cochranQ_lt_pos (hk : 2 ≤ Fintype.card ι) (θ : ℝ) :
    0 < P {ω | dlTau2Untruncated v (fun i => θ + b i ω + ε i ω) < 0} := by
  have hc := cochranQSlope_pos h.pos (by omega)
  set S : Set (ι → ℝ) := {x | dlTau2Untruncated v x < 0} with hS
  have hSopen : IsOpen S := isOpen_lt (continuous_dlTau2Untruncated v) continuous_const
  have hSne : (fun _ => θ : ι → ℝ) ∈ S := by
    change dlTau2Untruncated v (fun _ => θ) < 0
    have hQ : cochranQ v (fun _ => θ) = 0 := (cochranQ_eq_zero_iff h.pos _).2 fun _ _ => rfl
    rw [dlTau2Untruncated, hQ]
    have : (1 : ℝ) < Fintype.card ι := by exact_mod_cast hk
    exact div_neg_of_neg_of_pos (by linarith) hc
  have hopen : ∀ i, Measure.IsOpenPosMeasure (gaussianReal θ (v i + τ2).toNNReal) := fun i =>
    (gaussianReal_absolutelyContinuous' (v := (v i + τ2).toNNReal) θ (by
      rw [Ne, Real.toNNReal_eq_zero, not_le]
      exact add_pos_of_pos_of_nonneg (h.pos i) h.tau_nonneg)).isOpenPosMeasure
  have hpos : 0 < Measure.pi (fun i => gaussianReal θ (v i + τ2).toNNReal) S :=
    hSopen.measure_pos _ ⟨_, hSne⟩
  rw [← (h.hasLaw_pi θ).measure_eq (p := fun x => dlTau2Untruncated v x < 0)
    hSopen.measurableSet] at hpos
  exact hpos

/-- **Strict upward bias of the DerSimonian-Laird estimator**: in the Gaussian random effects
model with `k ≥ 2` studies, for every `τ² ≥ 0` the untruncated estimator is unbiased while the
truncated one is strictly biased upward, `τ² < E[τ̂²_DL]`. Proof: `τ̂²_DL - (Q - (k - 1)) / c`
is nonnegative and positive on `{Q < k - 1}`, an event of positive probability. -/
theorem lt_integral_dlTau2 (hk : 2 ≤ Fintype.card ι) (θ : ℝ) :
    ∫ ω, dlTau2Untruncated v (fun i => θ + b i ω + ε i ω) ∂P = τ2 ∧
      τ2 < ∫ ω, dlTau2 v (fun i => θ + b i ω + ε i ω) ∂P := by
  have := h.isRandomEffectsModel.isProbabilityMeasure
  obtain ⟨hRint, hE⟩ := h.isRandomEffectsModel.integral_dlTau2Untruncated hk θ
  refine ⟨hE, ?_⟩
  set R : Ω → ℝ := fun ω => dlTau2Untruncated v fun i => θ + b i ω + ε i ω with hR
  have hDint : Integrable (fun ω => max 0 (R ω) - R ω) P :=
    ((integrable_const 0).sup hRint).sub hRint
  have hDnn : 0 ≤ fun ω => max 0 (R ω) - R ω := fun ω => sub_nonneg.2 (le_max_right _ _)
  have hsupp : {ω | R ω < 0} ⊆ Function.support fun ω => max 0 (R ω) - R ω := by
    intro ω hω
    have hRω : R ω < 0 := hω
    simp only [Function.mem_support, max_eq_left hRω.le]
    exact sub_ne_zero.2 (ne_of_gt hRω)
  have hDpos : 0 < ∫ ω, max 0 (R ω) - R ω ∂P := by
    rw [integral_pos_iff_support_of_nonneg hDnn hDint]
    exact (h.measure_cochranQ_lt_pos hk θ).trans_le (measure_mono hsupp)
  have hsplit : ∫ ω, max 0 (R ω) ∂P = ∫ ω, R ω ∂P + ∫ ω, max 0 (R ω) - R ω ∂P := by
    rw [← integral_add hRint hDint]
    congr 1
    funext ω
    ring
  change τ2 < ∫ ω, max 0 (R ω) ∂P
  rw [hsplit, hE]
  linarith

end IsGaussianRandomEffectsModel

end MetaAnalysis

end CausalInference
