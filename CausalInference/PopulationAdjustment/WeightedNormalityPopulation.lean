/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.PopulationAdjustment.WeightedNormalityEquations

/-!
# The population tilt of the weighted estimator

The balance equations of entropy balancing have a population counterpart: the tilt `β₀` that
minimizes the population dual objective `F(β) = E[exp(βᵀ(φ(X) - t))]` (`tiltObjective`). This
file proves, under bounded features and the margin condition of `WeightedConsistencyFeasible`,
that `F` is continuous and coercive, has a global minimizer (`tiltMinimizer`), that the minimizer
solves the population balance equations `E[w_{β₀}(X) (φ(X) - t)] = 0`, and that it is separated
quantitatively: `F(β₀ + u) - F(β₀) ≥ c ‖u‖²` with an explicit `c > 0`. The separation gives the
uniqueness of the root of the population balance equations, which identifies the tilt in examples.

## Main definitions

* `tiltObjective`: the population dual objective `F(β) = E[w_β(X)]`.
* `tiltMinimizer`: a global minimizer of `F` (it exists and is unique under the margin condition).

## Main results

* `exists_isMinOn_tiltObjective`, `isMinOn_tiltMinimizer`: existence of the minimizer.
* `integral_tiltWeight_mul_sub_eq_zero`: the minimizer solves the population balance equations.
* `tiltObjective_sub_ge`: quadratic separation around a root of the balance equations.
* `tiltMinimizer_eq_of_balance`: a root of the population balance equations is the minimizer.

## References

* J. E. Signorovitch and coauthors, PharmacoEconomics 28 (2010).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Finset Matrix
open scoped Topology ENNReal

namespace CausalInference

namespace PopulationAdjustment

open PointTreatment

variable {𝒳 : Type*} {p : ℕ}

/-- The tilt factors along a sum of parameters. -/
theorem tiltWeight_add (φ : 𝒳 → Fin p → ℝ) (t β u : Fin p → ℝ) (x : 𝒳) :
    tiltWeight φ t 0 (β + u) x = tiltWeight φ t 0 β x * Real.exp (u ⬝ᵥ (φ x - t)) := by
  simp only [tiltWeight, zero_add, add_dotProduct, Real.exp_add]

/-- The tilt at zero is one. -/
theorem tiltWeight_zero_param (φ : 𝒳 → Fin p → ℝ) (t : Fin p → ℝ) (x : 𝒳) :
    tiltWeight φ t 0 0 x = 1 := by
  simp [tiltWeight]

/-- The tilt is continuous in the parameter. -/
theorem continuous_tiltWeight_param (φ : 𝒳 → Fin p → ℝ) (t : Fin p → ℝ) (x : 𝒳) :
    Continuous fun β : Fin p → ℝ => tiltWeight φ t 0 β x := by
  unfold tiltWeight
  exact (continuous_const.add (continuous_id.dotProduct continuous_const)).rexp

/-- A bound on the centered features against a direction. -/
theorem abs_dotProduct_feature_le {φ : 𝒳 → Fin p → ℝ} {t : Fin p → ℝ} {B : ℝ}
    (hB : ∀ x, ‖φ x - t‖ ≤ B) (u : Fin p → ℝ) (x : 𝒳) :
    |u ⬝ᵥ (φ x - t)| ≤ p * (‖u‖ * B) :=
  (abs_dotProduct_le_mul_norm u _).trans (mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_left (hB x) (norm_nonneg _)) (Nat.cast_nonneg p))

variable [MeasurableSpace 𝒳] {ν : Measure (𝒳 × Bool × ℝ)}

/-- The **population dual objective** of entropy balancing, `F(β) = E[exp(βᵀ(φ(X) - t))]`. -/
noncomputable def tiltObjective (ν : Measure (𝒳 × Bool × ℝ)) (φ : 𝒳 → Fin p → ℝ)
    (t β : Fin p → ℝ) : ℝ :=
  ∫ z, tiltWeight φ t 0 β z.1 ∂ν

open Classical in
/-- The **population tilt**: a global minimizer of the population dual objective, and `0` when
there is none (under the margin condition there is exactly one, `tiltMinimizer_eq_of_balance`). -/
noncomputable def tiltMinimizer (ν : Measure (𝒳 × Bool × ℝ)) (φ : 𝒳 → Fin p → ℝ)
    (t : Fin p → ℝ) : Fin p → ℝ :=
  if h : ∃ β, IsMinOn (tiltObjective ν φ t) Set.univ β then h.choose else 0

/-- The centered features against a direction are measurable. -/
theorem measurable_dotProduct_feature {φ : 𝒳 → Fin p → ℝ} (hφ : Measurable φ) (t u : Fin p → ℝ) :
    Measurable fun z : 𝒳 × Bool × ℝ => u ⬝ᵥ (φ z.1 - t) :=
  (continuous_const.dotProduct continuous_id).measurable.comp
    ((hφ.comp measurable_fst).sub_const t)

/-- The tilt times a bounded measurable function is integrable. -/
theorem integrable_tiltWeight_mul_of_abs_le [IsFiniteMeasure ν] {φ : 𝒳 → Fin p → ℝ}
    (hφ : Measurable φ) {t : Fin p → ℝ} {B : ℝ} (hB : ∀ x, ‖φ x - t‖ ≤ B) (β : Fin p → ℝ)
    {h : 𝒳 × Bool × ℝ → ℝ} (hm : Measurable h) {C : ℝ} (hC : ∀ z, |h z| ≤ C) :
    Integrable (fun z => tiltWeight φ t 0 β z.1 * h z) ν :=
  integrable_tiltWeight_mul hφ hB β (integrable_of_abs_le hm hC)

/-- The tilt is integrable. -/
theorem integrable_tiltWeight_fst [IsFiniteMeasure ν] {φ : 𝒳 → Fin p → ℝ}
    (hφ : Measurable φ) {t : Fin p → ℝ} {B : ℝ} (hB : ∀ x, ‖φ x - t‖ ≤ B) (β : Fin p → ℝ) :
    Integrable (fun z : 𝒳 × Bool × ℝ => tiltWeight φ t 0 β z.1) ν := by
  simpa using integrable_tiltWeight_mul (ν := ν) hφ hB β (integrable_const (1 : ℝ))

/-- A lower bound for an integral from a lower bound on a set. -/
theorem le_integral_of_le_on [IsFiniteMeasure ν] {f : 𝒳 × Bool × ℝ → ℝ} (hf : Integrable f ν)
    (hf0 : ∀ z, 0 ≤ f z) {S : Set (𝒳 × Bool × ℝ)} (hS : MeasurableSet S) {c : ℝ}
    (hfS : ∀ z ∈ S, c ≤ f z) : c * ν.real S ≤ ∫ z, f z ∂ν := by
  have hc : ∀ z, S.indicator (fun _ => c) z ≤ f z := fun z => by
    by_cases hz : z ∈ S
    · rw [Set.indicator_of_mem hz]; exact hfS z hz
    · rw [Set.indicator_of_notMem hz]; exact hf0 z
  calc c * ν.real S = ∫ z, S.indicator (fun _ => c) z ∂ν := by
        rw [integral_indicator_const c hS, smul_eq_mul, mul_comm]
    _ ≤ ∫ z, f z ∂ν := integral_mono ((integrable_const c).indicator hS) hf hc

/-- **The margin sets.** For a nonzero direction `u`, the set where `uᵀ(φ(X) - t) ≥ ‖u‖ δ` is
measurable and has probability at least `δ`. -/
theorem margin_set_of_ne_zero [IsFiniteMeasure ν] {φ : 𝒳 → Fin p → ℝ} (hφ : Measurable φ)
    {t : Fin p → ℝ} {δ : ℝ} (hmargin : ∀ v : Fin p → ℝ, ‖v‖ = 1 →
      δ ≤ ν.real {z | δ ≤ v ⬝ᵥ (φ z.1 - t)}) {u : Fin p → ℝ} (hu : u ≠ 0) :
    MeasurableSet {z : 𝒳 × Bool × ℝ | ‖u‖ * δ ≤ u ⬝ᵥ (φ z.1 - t)} ∧
      δ ≤ ν.real {z : 𝒳 × Bool × ℝ | ‖u‖ * δ ≤ u ⬝ᵥ (φ z.1 - t)} := by
  refine ⟨measurableSet_le measurable_const (measurable_dotProduct_feature hφ t u), ?_⟩
  have hu0 : 0 < ‖u‖ := norm_pos_iff.2 hu
  have hv : ‖‖u‖⁻¹ • u‖ = 1 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hu0), inv_mul_cancel₀ hu0.ne']
  refine (hmargin _ hv).trans (measureReal_mono fun z hz => ?_)
  simp only [Set.mem_ofPred_eq, smul_dotProduct, smul_eq_mul] at hz ⊢
  have := mul_le_mul_of_nonneg_left hz hu0.le
  rwa [← mul_assoc, mul_inv_cancel₀ hu0.ne', one_mul] at this

/-! ### Continuity, coercivity and existence -/

/-- The population dual objective is continuous. -/
theorem continuous_tiltObjective [IsFiniteMeasure ν] {φ : 𝒳 → Fin p → ℝ} (hφ : Measurable φ)
    {t : Fin p → ℝ} {B : ℝ} (hB : ∀ x, ‖φ x - t‖ ≤ B) :
    Continuous (tiltObjective ν φ t) := by
  refine continuous_iff_continuousAt.2 fun β₁ => ?_
  refine continuousAt_of_dominated (bound := fun _ => Real.exp (p * ((‖β₁‖ + 1) * B)))
    (Eventually.of_forall fun β => (measurable_tiltWeight_fst hφ t β).aestronglyMeasurable)
    ?_ (integrable_const _)
    (ae_of_all _ fun z => (continuous_tiltWeight_param φ t z.1).continuousAt)
  filter_upwards [Metric.ball_mem_nhds β₁ one_pos] with β hβ
  refine ae_of_all _ fun z => ?_
  rw [Real.norm_eq_abs, abs_of_pos (tiltWeight_pos _ _ _ _ _)]
  refine (tiltWeight_mem_Icc (hB z.1) ?_).2
  have := norm_le_of_mem_closedBall (Metric.ball_subset_closedBall hβ)
  linarith

/-- **Coercivity of the population dual objective**: `F(β) ≥ δ exp(δ ‖β‖)` for `β ≠ 0`. -/
theorem tiltObjective_ge [IsFiniteMeasure ν] {φ : 𝒳 → Fin p → ℝ} (hφ : Measurable φ)
    {t : Fin p → ℝ} {B : ℝ} (hB : ∀ x, ‖φ x - t‖ ≤ B) {δ : ℝ}
    (hmargin : ∀ v : Fin p → ℝ, ‖v‖ = 1 → δ ≤ ν.real {z | δ ≤ v ⬝ᵥ (φ z.1 - t)})
    {β : Fin p → ℝ} (hβ : β ≠ 0) :
    δ * Real.exp (δ * ‖β‖) ≤ tiltObjective ν φ t β := by
  obtain ⟨hS, hSδ⟩ := margin_set_of_ne_zero hφ hmargin hβ
  have h := le_integral_of_le_on (integrable_tiltWeight_fst (ν := ν) hφ hB β)
    (fun z => (tiltWeight_pos _ _ _ _ _).le) hS (c := Real.exp (δ * ‖β‖)) fun z hz => by
      simp only [Set.mem_ofPred_eq] at hz
      rw [tiltWeight, zero_add, mul_comm]
      exact Real.exp_le_exp.2 hz
  calc δ * Real.exp (δ * ‖β‖) ≤ Real.exp (δ * ‖β‖) * ν.real _ := by
        rw [mul_comm]; exact mul_le_mul_of_nonneg_left hSδ (Real.exp_pos _).le
    _ ≤ _ := h

/-- **Existence of the population tilt**: the population dual objective has a global minimizer. -/
theorem exists_isMinOn_tiltObjective [IsProbabilityMeasure ν] {φ : 𝒳 → Fin p → ℝ}
    (hφ : Measurable φ) {t : Fin p → ℝ} {B : ℝ} (hB : ∀ x, ‖φ x - t‖ ≤ B) {δ : ℝ} (hδ : 0 < δ)
    (hmargin : ∀ v : Fin p → ℝ, ‖v‖ = 1 → δ ≤ ν.real {z | δ ≤ v ⬝ᵥ (φ z.1 - t)}) :
    ∃ β, IsMinOn (tiltObjective ν φ t) Set.univ β := by
  have hF0 : tiltObjective ν φ t 0 = 1 := by simp [tiltObjective, tiltWeight_zero_param]
  obtain ⟨β₁, -, hmin⟩ := (isCompact_closedBall (0 : Fin p → ℝ) (1 / δ ^ 2)).exists_isMinOn
    ⟨0, Metric.mem_closedBall_self (by positivity)⟩
    (continuous_tiltObjective (ν := ν) hφ hB).continuousOn
  have hβ₁0 : tiltObjective ν φ t β₁ ≤ tiltObjective ν φ t 0 :=
    hmin (Metric.mem_closedBall_self (by positivity : (0 : ℝ) ≤ 1 / δ ^ 2))
  refine ⟨β₁, fun β _ => ?_⟩
  by_cases hβ : β ∈ Metric.closedBall (0 : Fin p → ℝ) (1 / δ ^ 2)
  · exact hmin hβ
  · have hR : 1 / δ ^ 2 < ‖β‖ := by simpa using hβ
    have hne : β ≠ 0 := by
      rintro rfl; rw [norm_zero] at hR; exact absurd hR (not_lt.2 (by positivity))
    have h1 := tiltObjective_ge (ν := ν) hφ hB hmargin hne
    have h2 : 1 < δ * Real.exp (δ * ‖β‖) := by
      have he : δ * (1 / δ ^ 2) = 1 / δ := by field_simp
      have h3 : Real.exp (1 / δ) ≤ Real.exp (δ * ‖β‖) := by
        rw [← he]; exact Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left hR.le hδ.le)
      have h4 : 1 / δ + 1 < Real.exp (1 / δ) := Real.add_one_lt_exp (by positivity)
      have h5 : δ * (1 / δ + 1) = 1 + δ := by field_simp
      nlinarith
    change tiltObjective ν φ t β₁ ≤ tiltObjective ν φ t β
    rw [hF0] at hβ₁0
    linarith

/-- The population tilt minimizes the population dual objective. -/
theorem isMinOn_tiltMinimizer [IsProbabilityMeasure ν] {φ : 𝒳 → Fin p → ℝ}
    (hφ : Measurable φ) {t : Fin p → ℝ} {B : ℝ} (hB : ∀ x, ‖φ x - t‖ ≤ B) {δ : ℝ} (hδ : 0 < δ)
    (hmargin : ∀ v : Fin p → ℝ, ‖v‖ = 1 → δ ≤ ν.real {z | δ ≤ v ⬝ᵥ (φ z.1 - t)}) :
    IsMinOn (tiltObjective ν φ t) Set.univ (tiltMinimizer ν φ t) := by
  have h := exists_isMinOn_tiltObjective hφ hB hδ hmargin
  simp only [tiltMinimizer, h, ↓reduceDIte]
  exact h.choose_spec

/-! ### The population balance equations -/

/-- The tilt times the exponential of a direction is integrable. -/
theorem integrable_tiltWeight_mul_exp [IsFiniteMeasure ν] {φ : 𝒳 → Fin p → ℝ}
    (hφ : Measurable φ) {t : Fin p → ℝ} {B : ℝ} (hB : ∀ x, ‖φ x - t‖ ≤ B) (β u : Fin p → ℝ) :
    Integrable (fun z => tiltWeight φ t 0 β z.1 * Real.exp (u ⬝ᵥ (φ z.1 - t))) ν :=
  integrable_tiltWeight_mul_of_abs_le hφ hB β
    (measurable_dotProduct_feature hφ t u).exp (C := Real.exp (p * (‖u‖ * B))) fun z => by
      rw [abs_of_pos (Real.exp_pos _)]
      exact Real.exp_le_exp.2 (le_of_abs_le (abs_dotProduct_feature_le hB u z.1))

/-- The tilt times `exp(uᵀΔ) - 1` is integrable. -/
theorem integrable_tiltWeight_mul_exp_sub_one [IsFiniteMeasure ν] {φ : 𝒳 → Fin p → ℝ}
    (hφ : Measurable φ) {t : Fin p → ℝ} {B : ℝ} (hB : ∀ x, ‖φ x - t‖ ≤ B) (β u : Fin p → ℝ) :
    Integrable (fun z => tiltWeight φ t 0 β z.1 * (Real.exp (u ⬝ᵥ (φ z.1 - t)) - 1)) ν := by
  refine ((integrable_tiltWeight_mul_exp hφ hB β u).sub
    (integrable_tiltWeight_fst hφ hB β)).congr (ae_of_all _ fun z => ?_)
  simp only [Pi.sub_apply]
  ring

/-- The increment of the dual objective: `F(β + u) - F(β) = E[w_β (exp(uᵀΔ) - 1)]`. -/
theorem tiltObjective_add_sub [IsFiniteMeasure ν] {φ : 𝒳 → Fin p → ℝ} (hφ : Measurable φ)
    {t : Fin p → ℝ} {B : ℝ} (hB : ∀ x, ‖φ x - t‖ ≤ B) (β u : Fin p → ℝ) :
    tiltObjective ν φ t (β + u) - tiltObjective ν φ t β =
      ∫ z, tiltWeight φ t 0 β z.1 * (Real.exp (u ⬝ᵥ (φ z.1 - t)) - 1) ∂ν := by
  simp only [mul_sub, mul_one, tiltObjective, tiltWeight_add]
  rw [integral_sub (integrable_tiltWeight_mul_exp hφ hB β u) (integrable_tiltWeight_fst hφ hB β)]

/-- A real number bounded by every small multiple of a constant is zero. -/
theorem eq_zero_of_abs_le_mul {g C η₀ : ℝ} (hη₀ : 0 < η₀) (hC : 0 ≤ C)
    (h : ∀ η, 0 < η → η ≤ η₀ → |g| ≤ η * C) : g = 0 := by
  by_contra hg
  have hg0 : 0 < |g| := abs_pos.2 hg
  set η := min η₀ (|g| / (2 * (C + 1))) with hη
  have hη0 : 0 < η := lt_min hη₀ (by positivity)
  have h1 := h η hη0 (min_le_left _ _)
  have h2 : η * C ≤ |g| / (2 * (C + 1)) * C :=
    mul_le_mul_of_nonneg_right (min_le_right _ _) hC
  have h3 : |g| / (2 * (C + 1)) * C < |g| := by
    rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
    nlinarith
  linarith

/-- **The population tilt solves the population balance equations**: at a global minimizer `β₀`
of `F`, `E[w_{β₀}(X) (φ(X)_j - t_j)] = 0` for every coordinate `j`. -/
theorem integral_tiltWeight_mul_sub_eq_zero [IsFiniteMeasure ν] {φ : 𝒳 → Fin p → ℝ}
    (hφ : Measurable φ) {t : Fin p → ℝ} {B : ℝ} (hB : ∀ x, ‖φ x - t‖ ≤ B) {β₀ : Fin p → ℝ}
    (hmin : IsMinOn (tiltObjective ν φ t) Set.univ β₀) (j : Fin p) :
    ∫ z, tiltWeight φ t 0 β₀ z.1 * (φ z.1 j - t j) ∂ν = 0 := by
  set L := |B| + 1 with hL
  have hL0 : 0 < L := by positivity
  have hΔ : ∀ z : 𝒳 × Bool × ℝ, |φ z.1 j - t j| ≤ L := fun z =>
    (abs_apply_le_of_norm_le (hB z.1) j).trans ((le_abs_self B).trans (by linarith))
  have hΔB : ∀ z : 𝒳 × Bool × ℝ, |φ z.1 j - t j| ≤ B := fun z => abs_apply_le_of_norm_le (hB z.1) j
  have hmΔ : Measurable fun z : 𝒳 × Bool × ℝ => φ z.1 j - t j :=
    (measurable_feature_fst hφ j).sub_const _
  have hi1 := integrable_tiltWeight_mul_of_abs_le (ν := ν) hφ hB β₀ hmΔ hΔB
  have hi2 := integrable_tiltWeight_mul_of_abs_le (ν := ν) hφ hB β₀ (hmΔ.pow_const 2)
    (C := B ^ 2) fun z => by
      rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) (hΔB z) 2
  set g := ∫ z, tiltWeight φ t 0 β₀ z.1 * (φ z.1 j - t j) ∂ν
  set C := ∫ z, tiltWeight φ t 0 β₀ z.1 * (φ z.1 j - t j) ^ 2 ∂ν
  have hC : 0 ≤ C := integral_nonneg fun z => mul_nonneg (tiltWeight_pos _ _ _ _ _).le (sq_nonneg _)
  have key : ∀ s : ℝ, |s| * L ≤ 1 → 0 ≤ s * g + s ^ 2 * C := by
    intro s hs
    have hd : ∀ z : 𝒳 × Bool × ℝ, Pi.single j s ⬝ᵥ (φ z.1 - t) = s * (φ z.1 j - t j) :=
      fun z => by rw [single_dotProduct, Pi.sub_apply]
    have h0 : 0 ≤ tiltObjective ν φ t (β₀ + Pi.single j s) - tiltObjective ν φ t β₀ :=
      sub_nonneg.2 (hmin (Set.mem_univ _))
    rw [tiltObjective_add_sub hφ hB] at h0
    refine h0.trans ?_
    have hint := integrable_tiltWeight_mul_exp_sub_one (ν := ν) hφ hB β₀ (Pi.single j s)
    have hrhs : s * g + s ^ 2 * C = ∫ z, (s * (tiltWeight φ t 0 β₀ z.1 * (φ z.1 j - t j)) +
        s ^ 2 * (tiltWeight φ t 0 β₀ z.1 * (φ z.1 j - t j) ^ 2)) ∂ν := by
      rw [integral_add (hi1.const_mul s) (hi2.const_mul _), integral_const_mul,
        integral_const_mul]
    rw [hrhs]
    refine integral_mono hint ((hi1.const_mul s).add (hi2.const_mul _)) fun z => ?_
    simp only [hd]
    have hx : |s * (φ z.1 j - t j)| ≤ 1 := by
      rw [abs_mul]
      exact (mul_le_mul_of_nonneg_left (hΔ z) (abs_nonneg s)).trans hs
    have he := le_of_abs_le (Real.abs_exp_sub_one_sub_id_le hx)
    have hw := (tiltWeight_pos φ t 0 β₀ z.1).le
    have : Real.exp (s * (φ z.1 j - t j)) - 1 ≤ s * (φ z.1 j - t j) +
        s ^ 2 * (φ z.1 j - t j) ^ 2 := by nlinarith
    calc tiltWeight φ t 0 β₀ z.1 * (Real.exp (s * (φ z.1 j - t j)) - 1)
        ≤ tiltWeight φ t 0 β₀ z.1 * (s * (φ z.1 j - t j) + s ^ 2 * (φ z.1 j - t j) ^ 2) :=
          mul_le_mul_of_nonneg_left this hw
      _ = _ := by ring
  refine eq_zero_of_abs_le_mul (inv_pos.2 hL0) hC fun η hη hηL => ?_
  have hηL' : |η| * L ≤ 1 := by
    rw [abs_of_pos hη]
    calc η * L ≤ L⁻¹ * L := mul_le_mul_of_nonneg_right hηL hL0.le
      _ = 1 := inv_mul_cancel₀ hL0.ne'
  have h1 := key η hηL'
  have h2 := key (-η) (by rwa [abs_neg])
  rw [abs_le]
  constructor <;> nlinarith

/-! ### Quadratic separation and uniqueness -/

/-- **Quadratic separation of the population objective** around a root `β` of the population
balance equations: for every direction `u`,
`F(β + u) - F(β) ≥ exp(-p ‖β‖ B) (‖u‖ δ)² / 2 · δ`. -/
theorem tiltObjective_sub_ge [IsFiniteMeasure ν] {φ : 𝒳 → Fin p → ℝ} (hφ : Measurable φ)
    {t : Fin p → ℝ} {B : ℝ} (hB : ∀ x, ‖φ x - t‖ ≤ B) {δ : ℝ} (hδ : 0 < δ)
    (hmargin : ∀ v : Fin p → ℝ, ‖v‖ = 1 → δ ≤ ν.real {z | δ ≤ v ⬝ᵥ (φ z.1 - t)})
    {β : Fin p → ℝ} (hbal : ∀ j, ∫ z, tiltWeight φ t 0 β z.1 * (φ z.1 j - t j) ∂ν = 0)
    (u : Fin p → ℝ) :
    Real.exp (-(p * (‖β‖ * B))) * (‖u‖ * δ) ^ 2 / 2 * δ ≤
      tiltObjective ν φ t (β + u) - tiltObjective ν φ t β := by
  rcases eq_or_ne u 0 with rfl | hu
  · simp
  rw [tiltObjective_add_sub hφ hB]
  have hlin : Integrable (fun z => tiltWeight φ t 0 β z.1 * (u ⬝ᵥ (φ z.1 - t))) ν :=
    integrable_tiltWeight_mul_of_abs_le hφ hB β (measurable_dotProduct_feature hφ t u)
      (abs_dotProduct_feature_le hB u ·.1)
  have hzero : ∫ z, tiltWeight φ t 0 β z.1 * (u ⬝ᵥ (φ z.1 - t)) ∂ν = 0 := by
    have hpt : ∀ z : 𝒳 × Bool × ℝ, tiltWeight φ t 0 β z.1 * (u ⬝ᵥ (φ z.1 - t)) =
        ∑ j, u j * (tiltWeight φ t 0 β z.1 * (φ z.1 j - t j)) := fun z => by
      simp only [dotProduct, Pi.sub_apply, Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => by ring
    simp_rw [hpt]
    rw [integral_finsetSum _ fun j _ => (integrable_tiltWeight_mul_of_abs_le hφ hB β
      ((measurable_feature_fst hφ j).sub_const _) fun z => abs_apply_le_of_norm_le (hB z.1) j
      ).const_mul _]
    simp [integral_const_mul, hbal]
  have hint := integrable_tiltWeight_mul_exp_sub_one (ν := ν) hφ hB β u
  have heq : ∫ z, tiltWeight φ t 0 β z.1 * (Real.exp (u ⬝ᵥ (φ z.1 - t)) - 1) ∂ν =
      ∫ z, tiltWeight φ t 0 β z.1 * (Real.exp (u ⬝ᵥ (φ z.1 - t)) - 1 - u ⬝ᵥ (φ z.1 - t)) ∂ν := by
    have := integral_sub hint hlin
    rw [hzero, sub_zero] at this
    rw [← this]
    congr 1; funext z; ring
  rw [heq]
  obtain ⟨hS, hSδ⟩ := margin_set_of_ne_zero hφ hmargin hu
  have hpos : ∀ x : ℝ, 0 ≤ Real.exp x - 1 - x := fun x => by linarith [Real.add_one_le_exp x]
  have hnorm : 0 ≤ ‖u‖ * δ := mul_nonneg (norm_nonneg _) hδ.le
  have h := le_integral_of_le_on (hint.sub hlin |>.congr (ae_of_all _ fun z => by
      simp only [Pi.sub_apply]; ring))
    (fun z => mul_nonneg (tiltWeight_pos _ _ _ _ _).le (hpos _)) hS
    (c := Real.exp (-(p * (‖β‖ * B))) * ((‖u‖ * δ) ^ 2 / 2)) fun z hz => by
      simp only [Set.mem_ofPred_eq] at hz
      have hx0 : 0 ≤ u ⬝ᵥ (φ z.1 - t) := hnorm.trans hz
      have hq := Real.quadratic_le_exp_of_nonneg hx0
      have hsq : (‖u‖ * δ) ^ 2 ≤ (u ⬝ᵥ (φ z.1 - t)) ^ 2 := pow_le_pow_left₀ hnorm hz 2
      exact mul_le_mul (tiltWeight_mem_Icc (hB z.1) le_rfl).1 (by linarith) (by positivity)
        (tiltWeight_pos _ _ _ _ _).le
  calc Real.exp (-(p * (‖β‖ * B))) * (‖u‖ * δ) ^ 2 / 2 * δ
      ≤ Real.exp (-(p * (‖β‖ * B))) * ((‖u‖ * δ) ^ 2 / 2) * ν.real _ := by
        rw [mul_div_assoc]; exact mul_le_mul_of_nonneg_left hSδ (by positivity)
    _ ≤ _ := h

/-- A root of the population balance equations minimizes the population objective. -/
theorem isMinOn_of_balance [IsFiniteMeasure ν] {φ : 𝒳 → Fin p → ℝ} (hφ : Measurable φ)
    {t : Fin p → ℝ} {B : ℝ} (hB : ∀ x, ‖φ x - t‖ ≤ B) {δ : ℝ} (hδ : 0 < δ)
    (hmargin : ∀ v : Fin p → ℝ, ‖v‖ = 1 → δ ≤ ν.real {z | δ ≤ v ⬝ᵥ (φ z.1 - t)})
    {β : Fin p → ℝ} (hbal : ∀ j, ∫ z, tiltWeight φ t 0 β z.1 * (φ z.1 j - t j) ∂ν = 0) :
    IsMinOn (tiltObjective ν φ t) Set.univ β := fun β' _ => by
  have h := tiltObjective_sub_ge hφ hB hδ hmargin hbal (β' - β)
  rw [add_sub_cancel] at h
  have : 0 ≤ Real.exp (-(p * (‖β‖ * B))) * (‖β' - β‖ * δ) ^ 2 / 2 * δ := by positivity
  change tiltObjective ν φ t β ≤ tiltObjective ν φ t β'
  linarith

/-- **Uniqueness of the population tilt**: a root of the population balance equations is the
population tilt. -/
theorem tiltMinimizer_eq_of_balance [IsProbabilityMeasure ν] {φ : 𝒳 → Fin p → ℝ}
    (hφ : Measurable φ) {t : Fin p → ℝ} {B : ℝ} (hB : ∀ x, ‖φ x - t‖ ≤ B) {δ : ℝ} (hδ : 0 < δ)
    (hmargin : ∀ v : Fin p → ℝ, ‖v‖ = 1 → δ ≤ ν.real {z | δ ≤ v ⬝ᵥ (φ z.1 - t)})
    {β : Fin p → ℝ} (hbal : ∀ j, ∫ z, tiltWeight φ t 0 β z.1 * (φ z.1 j - t j) ∂ν = 0) :
    tiltMinimizer ν φ t = β := by
  have hmin : tiltObjective ν φ t (tiltMinimizer ν φ t) ≤ tiltObjective ν φ t β :=
    isMinOn_tiltMinimizer hφ hB hδ hmargin (Set.mem_univ β)
  have h := tiltObjective_sub_ge hφ hB hδ hmargin hbal (tiltMinimizer ν φ t - β)
  rw [add_sub_cancel] at h
  have h0 : Real.exp (-(p * (‖β‖ * B))) * (‖tiltMinimizer ν φ t - β‖ * δ) ^ 2 / 2 * δ ≤ 0 := by
    linarith
  have hn : ‖tiltMinimizer ν φ t - β‖ = 0 := by
    by_contra hne
    have : 0 < Real.exp (-(p * (‖β‖ * B))) * (‖tiltMinimizer ν φ t - β‖ * δ) ^ 2 / 2 * δ := by
      have := (norm_nonneg (tiltMinimizer ν φ t - β)).lt_of_ne' hne
      positivity
    linarith
  exact sub_eq_zero.1 (norm_eq_zero.1 hn)

/-- The population tilt solves the population balance equations. -/
theorem integral_tiltWeight_tiltMinimizer_mul_sub [IsProbabilityMeasure ν] {φ : 𝒳 → Fin p → ℝ}
    (hφ : Measurable φ) {t : Fin p → ℝ} {B : ℝ} (hB : ∀ x, ‖φ x - t‖ ≤ B) {δ : ℝ} (hδ : 0 < δ)
    (hmargin : ∀ v : Fin p → ℝ, ‖v‖ = 1 → δ ≤ ν.real {z | δ ≤ v ⬝ᵥ (φ z.1 - t)}) (j : Fin p) :
    ∫ z, tiltWeight φ t 0 (tiltMinimizer ν φ t) z.1 * (φ z.1 j - t j) ∂ν = 0 :=
  integral_tiltWeight_mul_sub_eq_zero hφ hB (isMinOn_tiltMinimizer hφ hB hδ hmargin) j

end PopulationAdjustment

end CausalInference
